module

public import SpectreFinite.RadiusFiveRoot8Part4
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable1
public import SpectreFinite.RadiusFiveTable13
public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node9Domains0 : Domains 91 State := restrict root8Node1Domains4 0 (8,4)
def root8Node9Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0),(6,4)]
  | 2 => some [(1,2),(3,2),(7,2)]
  | 3 => some [(4,0),(7,4),(8,4)]
  | 4 => some [(0,0),(1,3),(7,3)]
  | 5 => some [(5,2),(7,2),(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5),(7,5)]
  | 8 => some [(0,3),(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(1,5),(6,5)]
  | 11 => some [(0,4),(6,1),(6,2)]
  | 12 => some [(5,1),(5,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,0)]
  | 14 => some [(4,5),(7,3),(8,5)]
  | 15 => some [(4,2),(7,0)]
  | 16 => some [(5,3),(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3),(6,4)]
  | 23 => some [(1,2),(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(6,3),(7,3)]
  | 29 => some [(2,2),(4,2),(8,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5),(3,5),(7,5)]
  | 32 => some [(0,3),(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(5,1),(8,1)]
  | 37 => some [(0,1),(0,2),(6,5)]
  | 38 => some [(0,4),(1,1),(6,2)]
  | 39 => some [(0,1),(1,4),(3,4),(5,4),(7,4)]
  | 40 => some [(0,0),(1,4),(6,4),(7,4)]
  | 41 => some [(0,5),(1,2),(3,2),(6,3)]
  | 42 => some [(2,0),(2,2),(2,4),(4,0)]
  | 43 => some [(1,3),(3,3),(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(1,0),(3,0),(5,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => some [(0,2),(0,3),(6,0),(6,1)]
  | 52 => some [(1,1),(3,1),(5,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(3,2),(7,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0),(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(7,4),(8,0)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(5,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(0,4),(1,1),(6,1)]
  | 79 => some [(5,1),(5,4),(8,1)]
  | 80 => some [(0,1),(6,4),(6,5)]
  | 81 => some [(0,4),(1,2),(6,2)]
  | 82 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => some [(0,0),(0,5),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => some [(0,3),(1,1),(6,1),(7,1)]
theorem root8Node9Domains0_fast_eq : root8Node9Domains0 = expandDomains root8Node9Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node9Domains0 v = expandDomains root8Node9Domains0Fast v from by decide) v
def root8Node9Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0),(6,4)]
  | 2 => [(1,2),(7,2)]
  | 3 => [(4,0),(7,4),(8,4)]
  | 4 => [(0,0),(1,3),(7,3)]
  | 5 => [(7,2),(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(1,5),(7,5)]
  | 8 => [(0,3),(6,1)]
  | 9 => [(5,1),(8,1)]
  | 10 => [(0,1),(1,5),(6,5)]
  | 11 => [(0,4),(6,1),(6,2)]
  | 12 => [(5,1),(5,4),(8,4)]
  | 13 => [(5,0),(5,3),(8,0)]
  | 14 => [(4,5),(7,3),(8,5)]
  | 15 => [(4,2),(7,0)]
  | 16 => [(5,3),(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0),(7,0)]
  | 19 => [(4,3),(7,1),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(3,4),(5,4),(7,4)]
  | 22 => [(0,0),(6,3),(6,4)]
  | 23 => [(1,2),(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(6,3),(7,3)]
  | 29 => [(2,2),(4,2),(8,2)]
  | 30 => [(2,1),(2,3),(4,3)]
  | 31 => [(0,2),(1,5),(3,5),(7,5)]
  | 32 => [(0,3),(1,1),(6,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(5,1),(8,1)]
  | 37 => [(0,1),(0,2),(6,5)]
  | 38 => [(0,4),(1,1),(6,2)]
  | 39 => [(0,1),(1,4),(3,4),(5,4),(7,4)]
  | 40 => [(0,0),(1,4),(6,4),(7,4)]
  | 41 => [(0,5),(1,2),(3,2),(6,3)]
  | 42 => [(2,0),(2,2),(2,4),(4,0)]
  | 43 => [(1,3),(3,3),(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(1,0),(3,0),(5,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => [(0,2),(0,3),(6,0),(6,1)]
  | 52 => [(1,1),(3,1),(5,1),(7,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(1,4),(6,4)]
  | 60 => [(0,5),(1,2),(3,2),(7,2)]
  | 61 => [(5,0),(5,3),(8,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3),(6,0)]
  | 67 => [(7,1),(8,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,0),(6,1)]
  | 70 => [(0,0),(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(7,4),(8,0)]
  | 73 => [(1,3),(7,3)]
  | 74 => [(4,2),(8,2)]
  | 75 => [(5,0),(5,3),(8,0)]
  | 76 => [(4,5),(5,5),(7,3),(8,5)]
  | 77 => [(4,2),(7,0),(8,2)]
  | 78 => [(0,4),(1,1),(6,1)]
  | 79 => [(5,1),(5,4),(8,1)]
  | 80 => [(0,1),(6,4),(6,5)]
  | 81 => [(0,4),(1,2),(6,2)]
  | 82 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => [(0,0),(0,5),(6,3),(6,4)]
  | 84 => [(1,2),(4,4),(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5),(7,5),(8,5)]
  | 87 => [(0,3),(1,0),(3,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => [(0,3),(1,1),(6,1),(7,1)]
def root8Node9Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0),(6,4)]
  | 2 => some [(1,2),(7,2)]
  | 3 => some [(4,0),(7,4),(8,4)]
  | 4 => some [(0,0),(1,3),(7,3)]
  | 5 => some [(7,2),(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5),(7,5)]
  | 8 => some [(0,3),(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(1,5),(6,5)]
  | 11 => some [(0,4),(6,1),(6,2)]
  | 12 => some [(5,1),(5,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,0)]
  | 14 => some [(4,5),(7,3),(8,5)]
  | 15 => some [(4,2),(7,0)]
  | 16 => some [(5,3),(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3),(6,4)]
  | 23 => some [(1,2),(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(6,3),(7,3)]
  | 29 => some [(2,2),(4,2),(8,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5),(3,5),(7,5)]
  | 32 => some [(0,3),(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(5,1),(8,1)]
  | 37 => some [(0,1),(0,2),(6,5)]
  | 38 => some [(0,4),(1,1),(6,2)]
  | 39 => some [(0,1),(1,4),(3,4),(5,4),(7,4)]
  | 40 => some [(0,0),(1,4),(6,4),(7,4)]
  | 41 => some [(0,5),(1,2),(3,2),(6,3)]
  | 42 => some [(2,0),(2,2),(2,4),(4,0)]
  | 43 => some [(1,3),(3,3),(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(1,0),(3,0),(5,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => some [(0,2),(0,3),(6,0),(6,1)]
  | 52 => some [(1,1),(3,1),(5,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(3,2),(7,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0),(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(7,4),(8,0)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(5,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(0,4),(1,1),(6,1)]
  | 79 => some [(5,1),(5,4),(8,1)]
  | 80 => some [(0,1),(6,4),(6,5)]
  | 81 => some [(0,4),(1,2),(6,2)]
  | 82 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => some [(0,0),(0,5),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => some [(0,3),(1,1),(6,1),(7,1)]
theorem root8Node9Domains1_fast_eq : root8Node9Domains1 = expandDomains root8Node9Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node9Domains1 v = expandDomains root8Node9Domains1Fast v from by decide) v
theorem root8Node9Step1Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq (by decide)
theorem root8Node9Step1Narrowing_checked :
    checkNarrowing table1 root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkNarrowing_flatten table1Scope [table1Rows0_0,table1Rows0_1,table1Rows0_2,table1Rows0_3,table1Rows0_4,table1Rows0_5,table1Rows1_0,table1Rows1_1,table1Rows1_2,table1Rows1_3,table1Rows1_4,table1Rows1_5,table1Rows2_0,table1Rows2_1,table1Rows2_2,table1Rows2_3,table1Rows2_4,table1Rows2_5,table1Rows3_0,table1Rows3_1,table1Rows3_2,table1Rows3_3,table1Rows3_4,table1Rows3_5,table1Rows4_0,table1Rows4_1,table1Rows4_2,table1Rows4_3,table1Rows4_4,table1Rows4_5,table1Rows5_0,table1Rows5_1,table1Rows5_2,table1Rows5_3,table1Rows5_4,table1Rows5_5,table1Rows6_0,table1Rows6_1,table1Rows6_2,table1Rows6_3,table1Rows6_4,table1Rows6_5,table1Rows7_0,table1Rows7_1,table1Rows7_2,table1Rows7_3,table1Rows7_4,table1Rows7_5,table1Rows8_0,table1Rows8_1,table1Rows8_2,table1Rows8_3,table1Rows8_4,table1Rows8_5]
    root8Node9Domains0 root8Node9Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node9Step1Chunk0_0_checked, root8Node9Step1Chunk0_1_checked, root8Node9Step1Chunk0_2_checked, root8Node9Step1Chunk0_3_checked, root8Node9Step1Chunk0_4_checked, root8Node9Step1Chunk0_5_checked, root8Node9Step1Chunk1_0_checked, root8Node9Step1Chunk1_1_checked, root8Node9Step1Chunk1_2_checked, root8Node9Step1Chunk1_3_checked, root8Node9Step1Chunk1_4_checked, root8Node9Step1Chunk1_5_checked, root8Node9Step1Chunk2_0_checked, root8Node9Step1Chunk2_1_checked, root8Node9Step1Chunk2_2_checked, root8Node9Step1Chunk2_3_checked, root8Node9Step1Chunk2_4_checked, root8Node9Step1Chunk2_5_checked, root8Node9Step1Chunk3_0_checked, root8Node9Step1Chunk3_1_checked, root8Node9Step1Chunk3_2_checked, root8Node9Step1Chunk3_3_checked, root8Node9Step1Chunk3_4_checked, root8Node9Step1Chunk3_5_checked, root8Node9Step1Chunk4_0_checked, root8Node9Step1Chunk4_1_checked, root8Node9Step1Chunk4_2_checked, root8Node9Step1Chunk4_3_checked, root8Node9Step1Chunk4_4_checked, root8Node9Step1Chunk4_5_checked, root8Node9Step1Chunk5_0_checked, root8Node9Step1Chunk5_1_checked, root8Node9Step1Chunk5_2_checked, root8Node9Step1Chunk5_3_checked, root8Node9Step1Chunk5_4_checked, root8Node9Step1Chunk5_5_checked, root8Node9Step1Chunk6_0_checked, root8Node9Step1Chunk6_1_checked, root8Node9Step1Chunk6_2_checked, root8Node9Step1Chunk6_3_checked, root8Node9Step1Chunk6_4_checked, root8Node9Step1Chunk6_5_checked, root8Node9Step1Chunk7_0_checked, root8Node9Step1Chunk7_1_checked, root8Node9Step1Chunk7_2_checked, root8Node9Step1Chunk7_3_checked, root8Node9Step1Chunk7_4_checked, root8Node9Step1Chunk7_5_checked, root8Node9Step1Chunk8_0_checked, root8Node9Step1Chunk8_1_checked, root8Node9Step1Chunk8_2_checked, root8Node9Step1Chunk8_3_checked, root8Node9Step1Chunk8_4_checked, root8Node9Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node9Step1_checked :
    checkReplacement table1 root8Node9Domains0 root8Node9Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node9Domains0 root8Node9Domains1
    root8Node9Domains0Fast root8Node9Domains1Fast
    root8Node9Domains0_fast_eq root8Node9Domains1_fast_eq
    root8Node9Step1Narrowing_checked (by decide)
def root8Node10Domains0 : Domains 91 State := restrict root8Node9Domains1 1 (0,0)
def root8Node10Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(1,2),(7,2)]
  | 3 => some [(4,0),(7,4),(8,4)]
  | 4 => some [(0,0),(1,3),(7,3)]
  | 5 => some [(7,2),(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5),(7,5)]
  | 8 => some [(0,3),(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(1,5),(6,5)]
  | 11 => some [(0,4),(6,1),(6,2)]
  | 12 => some [(5,1),(5,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,0)]
  | 14 => some [(4,5),(7,3),(8,5)]
  | 15 => some [(4,2),(7,0)]
  | 16 => some [(5,3),(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3),(6,4)]
  | 23 => some [(1,2),(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(6,3),(7,3)]
  | 29 => some [(2,2),(4,2),(8,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5),(3,5),(7,5)]
  | 32 => some [(0,3),(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(5,1),(8,1)]
  | 37 => some [(0,1),(0,2),(6,5)]
  | 38 => some [(0,4),(1,1),(6,2)]
  | 39 => some [(0,1),(1,4),(3,4),(5,4),(7,4)]
  | 40 => some [(0,0),(1,4),(6,4),(7,4)]
  | 41 => some [(0,5),(1,2),(3,2),(6,3)]
  | 42 => some [(2,0),(2,2),(2,4),(4,0)]
  | 43 => some [(1,3),(3,3),(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(1,0),(3,0),(5,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => some [(0,2),(0,3),(6,0),(6,1)]
  | 52 => some [(1,1),(3,1),(5,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(3,2),(7,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0),(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(7,4),(8,0)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(5,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(0,4),(1,1),(6,1)]
  | 79 => some [(5,1),(5,4),(8,1)]
  | 80 => some [(0,1),(6,4),(6,5)]
  | 81 => some [(0,4),(1,2),(6,2)]
  | 82 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => some [(0,0),(0,5),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => some [(0,3),(1,1),(6,1),(7,1)]
theorem root8Node10Domains0_fast_eq : root8Node10Domains0 = expandDomains root8Node10Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node10Domains0 v = expandDomains root8Node10Domains0Fast v from by decide) v
def root8Node10Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(7,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1),(8,1)]
  | 10 => [(0,1),(6,5)]
  | 11 => [(0,4),(6,2)]
  | 12 => [(5,4),(8,4)]
  | 13 => [(5,0),(5,3),(8,0)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0),(7,0)]
  | 19 => [(4,3),(7,1)]
  | 20 => [(7,5)]
  | 21 => [(3,4),(5,4),(7,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(6,3),(7,3)]
  | 29 => [(2,2),(4,2)]
  | 30 => [(2,1),(2,3),(4,3)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(5,1),(8,1)]
  | 37 => [(0,1),(0,2),(6,5)]
  | 38 => [(0,4),(1,1),(6,2)]
  | 39 => [(0,1),(1,4),(3,4),(7,4)]
  | 40 => [(0,0),(1,4),(6,4),(7,4)]
  | 41 => [(0,5),(1,2),(3,2),(6,3)]
  | 42 => [(2,0),(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(1,0),(3,0),(5,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => [(0,2),(0,3),(6,0),(6,1)]
  | 52 => [(1,1),(3,1),(5,1),(7,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(6,4)]
  | 60 => [(0,5),(1,2),(3,2),(7,2)]
  | 61 => [(5,0),(5,3),(8,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3),(6,0)]
  | 67 => [(7,1),(8,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,0),(6,1)]
  | 70 => [(0,0),(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2),(8,2)]
  | 75 => [(5,0),(5,3),(8,0)]
  | 76 => [(4,5),(7,3),(8,5)]
  | 77 => [(4,2),(7,0),(8,2)]
  | 78 => [(0,4),(1,1),(6,1)]
  | 79 => [(5,1),(5,4),(8,1)]
  | 80 => [(0,1),(6,4),(6,5)]
  | 81 => [(0,4),(1,2),(6,2)]
  | 82 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => [(0,0),(0,5),(6,3),(6,4)]
  | 84 => [(1,2),(4,4),(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5),(7,5),(8,5)]
  | 87 => [(0,3),(1,0),(3,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => [(0,3),(1,1),(6,1),(7,1)]
def root8Node10Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(6,5)]
  | 11 => some [(0,4),(6,2)]
  | 12 => some [(5,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,0)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(6,3),(7,3)]
  | 29 => some [(2,2),(4,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(5,1),(8,1)]
  | 37 => some [(0,1),(0,2),(6,5)]
  | 38 => some [(0,4),(1,1),(6,2)]
  | 39 => some [(0,1),(1,4),(3,4),(7,4)]
  | 40 => some [(0,0),(1,4),(6,4),(7,4)]
  | 41 => some [(0,5),(1,2),(3,2),(6,3)]
  | 42 => some [(2,0),(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(1,0),(3,0),(5,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => some [(0,2),(0,3),(6,0),(6,1)]
  | 52 => some [(1,1),(3,1),(5,1),(7,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(0,5),(1,2),(3,2),(7,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0),(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(0,4),(1,1),(6,1)]
  | 79 => some [(5,1),(5,4),(8,1)]
  | 80 => some [(0,1),(6,4),(6,5)]
  | 81 => some [(0,4),(1,2),(6,2)]
  | 82 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => some [(0,0),(0,5),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5),(8,5)]
  | 87 => some [(0,3),(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => some [(0,3),(1,1),(6,1),(7,1)]
theorem root8Node10Domains1_fast_eq : root8Node10Domains1 = expandDomains root8Node10Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node10Domains1 v = expandDomains root8Node10Domains1Fast v from by decide) v
theorem root8Node10Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq (by decide)
theorem root8Node10Step1Narrowing_checked :
    checkNarrowing table35 root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkNarrowing_flatten table35Scope [table35Rows0_0,table35Rows0_1,table35Rows0_2,table35Rows0_3,table35Rows0_4,table35Rows0_5,table35Rows1_0,table35Rows1_1,table35Rows1_2,table35Rows1_3,table35Rows1_4,table35Rows1_5,table35Rows2_0,table35Rows2_1,table35Rows2_2,table35Rows2_3,table35Rows2_4,table35Rows2_5,table35Rows3_0,table35Rows3_1,table35Rows3_2,table35Rows3_3,table35Rows3_4,table35Rows3_5,table35Rows4_0,table35Rows4_1,table35Rows4_2,table35Rows4_3,table35Rows4_4,table35Rows4_5,table35Rows5_0,table35Rows5_1,table35Rows5_2,table35Rows5_3,table35Rows5_4,table35Rows5_5,table35Rows6_0,table35Rows6_1,table35Rows6_2,table35Rows6_3,table35Rows6_4,table35Rows6_5,table35Rows7_0,table35Rows7_1,table35Rows7_2,table35Rows7_3,table35Rows7_4,table35Rows7_5,table35Rows8_0,table35Rows8_1,table35Rows8_2,table35Rows8_3,table35Rows8_4,table35Rows8_5]
    root8Node10Domains0 root8Node10Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node10Step1Chunk0_0_checked, root8Node10Step1Chunk0_1_checked, root8Node10Step1Chunk0_2_checked, root8Node10Step1Chunk0_3_checked, root8Node10Step1Chunk0_4_checked, root8Node10Step1Chunk0_5_checked, root8Node10Step1Chunk1_0_checked, root8Node10Step1Chunk1_1_checked, root8Node10Step1Chunk1_2_checked, root8Node10Step1Chunk1_3_checked, root8Node10Step1Chunk1_4_checked, root8Node10Step1Chunk1_5_checked, root8Node10Step1Chunk2_0_checked, root8Node10Step1Chunk2_1_checked, root8Node10Step1Chunk2_2_checked, root8Node10Step1Chunk2_3_checked, root8Node10Step1Chunk2_4_checked, root8Node10Step1Chunk2_5_checked, root8Node10Step1Chunk3_0_checked, root8Node10Step1Chunk3_1_checked, root8Node10Step1Chunk3_2_checked, root8Node10Step1Chunk3_3_checked, root8Node10Step1Chunk3_4_checked, root8Node10Step1Chunk3_5_checked, root8Node10Step1Chunk4_0_checked, root8Node10Step1Chunk4_1_checked, root8Node10Step1Chunk4_2_checked, root8Node10Step1Chunk4_3_checked, root8Node10Step1Chunk4_4_checked, root8Node10Step1Chunk4_5_checked, root8Node10Step1Chunk5_0_checked, root8Node10Step1Chunk5_1_checked, root8Node10Step1Chunk5_2_checked, root8Node10Step1Chunk5_3_checked, root8Node10Step1Chunk5_4_checked, root8Node10Step1Chunk5_5_checked, root8Node10Step1Chunk6_0_checked, root8Node10Step1Chunk6_1_checked, root8Node10Step1Chunk6_2_checked, root8Node10Step1Chunk6_3_checked, root8Node10Step1Chunk6_4_checked, root8Node10Step1Chunk6_5_checked, root8Node10Step1Chunk7_0_checked, root8Node10Step1Chunk7_1_checked, root8Node10Step1Chunk7_2_checked, root8Node10Step1Chunk7_3_checked, root8Node10Step1Chunk7_4_checked, root8Node10Step1Chunk7_5_checked, root8Node10Step1Chunk8_0_checked, root8Node10Step1Chunk8_1_checked, root8Node10Step1Chunk8_2_checked, root8Node10Step1Chunk8_3_checked, root8Node10Step1Chunk8_4_checked, root8Node10Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node10Step1_checked :
    checkReplacement table35 root8Node10Domains0 root8Node10Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node10Domains0 root8Node10Domains1
    root8Node10Domains0Fast root8Node10Domains1Fast
    root8Node10Domains0_fast_eq root8Node10Domains1_fast_eq
    root8Node10Step1Narrowing_checked (by decide)
def root8Node10Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(7,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1),(8,1)]
  | 10 => [(0,1),(6,5)]
  | 11 => [(0,4),(6,2)]
  | 12 => [(5,4),(8,4)]
  | 13 => [(5,0),(5,3),(8,0)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0),(7,0)]
  | 19 => [(4,3),(7,1)]
  | 20 => [(7,5)]
  | 21 => [(3,4),(5,4),(7,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(6,3),(7,3)]
  | 29 => [(2,2),(4,2)]
  | 30 => [(2,1),(2,3),(4,3)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(5,1),(8,1)]
  | 37 => [(0,1),(0,2),(6,5)]
  | 38 => [(0,4),(1,1),(6,2)]
  | 39 => [(0,1),(1,4),(3,4),(7,4)]
  | 40 => [(0,0),(1,4),(6,4),(7,4)]
  | 41 => [(0,5),(1,2),(3,2),(6,3)]
  | 42 => [(2,0),(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(1,0),(3,0),(5,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => [(0,2),(0,3),(6,0),(6,1)]
  | 52 => [(3,1),(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(6,4)]
  | 60 => [(1,2),(3,2),(7,2)]
  | 61 => [(5,0),(5,3),(8,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3),(6,0)]
  | 67 => [(7,1),(8,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,1)]
  | 70 => [(0,0),(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2),(8,2)]
  | 75 => [(5,0),(5,3),(8,0)]
  | 76 => [(4,5),(7,3),(8,5)]
  | 77 => [(4,2),(7,0)]
  | 78 => [(0,4),(1,1),(6,1)]
  | 79 => [(5,1),(5,4)]
  | 80 => [(0,1),(6,4)]
  | 81 => [(1,2),(6,2)]
  | 82 => [(7,4),(8,4)]
  | 83 => [(0,0),(6,3),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5),(7,5),(8,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(2,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(7,5)]
  | _ => [(0,3),(1,1),(6,1)]
def root8Node10Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(6,5)]
  | 11 => some [(0,4),(6,2)]
  | 12 => some [(5,4),(8,4)]
  | 13 => some [(5,0),(5,3),(8,0)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(6,3),(7,3)]
  | 29 => some [(2,2),(4,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(5,1),(8,1)]
  | 37 => some [(0,1),(0,2),(6,5)]
  | 38 => some [(0,4),(1,1),(6,2)]
  | 39 => some [(0,1),(1,4),(3,4),(7,4)]
  | 40 => some [(0,0),(1,4),(6,4),(7,4)]
  | 41 => some [(0,5),(1,2),(3,2),(6,3)]
  | 42 => some [(2,0),(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(1,0),(3,0),(5,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => some [(0,2),(0,3),(6,0),(6,1)]
  | 52 => some [(3,1),(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(3,2),(7,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0),(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(0,4),(1,1),(6,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4),(8,4)]
  | 83 => some [(0,0),(6,3),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(7,5)]
  | _ => some [(0,3),(1,1),(6,1)]
theorem root8Node10Domains2_fast_eq : root8Node10Domains2 = expandDomains root8Node10Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node10Domains2 v = expandDomains root8Node10Domains2Fast v from by decide) v
theorem root8Node10Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq (by decide)
theorem root8Node10Step2Narrowing_checked :
    checkNarrowing table56 root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node10Domains1 root8Node10Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node10Step2Chunk0_0_checked, root8Node10Step2Chunk0_1_checked, root8Node10Step2Chunk0_2_checked, root8Node10Step2Chunk0_3_checked, root8Node10Step2Chunk0_4_checked, root8Node10Step2Chunk0_5_checked, root8Node10Step2Chunk1_0_checked, root8Node10Step2Chunk1_1_checked, root8Node10Step2Chunk1_2_checked, root8Node10Step2Chunk1_3_checked, root8Node10Step2Chunk1_4_checked, root8Node10Step2Chunk1_5_checked, root8Node10Step2Chunk2_0_checked, root8Node10Step2Chunk2_1_checked, root8Node10Step2Chunk2_2_checked, root8Node10Step2Chunk2_3_checked, root8Node10Step2Chunk2_4_checked, root8Node10Step2Chunk2_5_checked, root8Node10Step2Chunk3_0_checked, root8Node10Step2Chunk3_1_checked, root8Node10Step2Chunk3_2_checked, root8Node10Step2Chunk3_3_checked, root8Node10Step2Chunk3_4_checked, root8Node10Step2Chunk3_5_checked, root8Node10Step2Chunk4_0_checked, root8Node10Step2Chunk4_1_checked, root8Node10Step2Chunk4_2_checked, root8Node10Step2Chunk4_3_checked, root8Node10Step2Chunk4_4_checked, root8Node10Step2Chunk4_5_checked, root8Node10Step2Chunk5_0_checked, root8Node10Step2Chunk5_1_checked, root8Node10Step2Chunk5_2_checked, root8Node10Step2Chunk5_3_checked, root8Node10Step2Chunk5_4_checked, root8Node10Step2Chunk5_5_checked, root8Node10Step2Chunk6_0_checked, root8Node10Step2Chunk6_1_checked, root8Node10Step2Chunk6_2_checked, root8Node10Step2Chunk6_3_checked, root8Node10Step2Chunk6_4_checked, root8Node10Step2Chunk6_5_checked, root8Node10Step2Chunk7_0_checked, root8Node10Step2Chunk7_1_checked, root8Node10Step2Chunk7_2_checked, root8Node10Step2Chunk7_3_checked, root8Node10Step2Chunk7_4_checked, root8Node10Step2Chunk7_5_checked, root8Node10Step2Chunk8_0_checked, root8Node10Step2Chunk8_1_checked, root8Node10Step2Chunk8_2_checked, root8Node10Step2Chunk8_3_checked, root8Node10Step2Chunk8_4_checked, root8Node10Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node10Step2_checked :
    checkReplacement table56 root8Node10Domains1 root8Node10Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node10Domains1 root8Node10Domains2
    root8Node10Domains1Fast root8Node10Domains2Fast
    root8Node10Domains1_fast_eq root8Node10Domains2_fast_eq
    root8Node10Step2Narrowing_checked (by decide)
def root8Node10Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(7,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1),(8,1)]
  | 7 => [(1,5)]
  | 8 => [(6,1)]
  | 9 => [(5,1),(8,1)]
  | 10 => [(0,1),(6,5)]
  | 11 => [(0,4),(6,2)]
  | 12 => [(5,4),(8,4)]
  | 13 => [(5,0),(5,3)]
  | 14 => [(4,5),(8,5)]
  | 15 => [(7,0)]
  | 16 => [(8,3)]
  | 17 => [(8,5)]
  | 18 => [(1,0),(7,0)]
  | 19 => [(4,3),(7,1)]
  | 20 => [(7,5)]
  | 21 => [(3,4),(5,4),(7,4)]
  | 22 => [(0,0),(6,3)]
  | 23 => [(7,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(6,3),(7,3)]
  | 29 => [(2,2),(4,2)]
  | 30 => [(2,1),(2,3),(4,3)]
  | 31 => [(0,2),(1,5)]
  | 32 => [(1,1),(6,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(5,1),(8,1)]
  | 37 => [(0,1),(0,2),(6,5)]
  | 38 => [(0,4),(1,1),(6,2)]
  | 39 => [(0,1),(1,4),(3,4),(7,4)]
  | 40 => [(0,0),(1,4),(6,4)]
  | 41 => [(0,5),(1,2),(3,2)]
  | 42 => [(2,0),(4,0)]
  | 43 => [(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(1,0),(3,0),(5,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => [(0,3),(6,0),(6,1)]
  | 52 => [(3,1),(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(6,4)]
  | 60 => [(1,2),(3,2),(7,2)]
  | 61 => [(5,0),(5,3),(8,3)]
  | 62 => [(4,5),(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3),(6,0)]
  | 67 => [(7,1),(8,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,1)]
  | 70 => [(0,0),(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2),(8,2)]
  | 75 => [(5,0),(5,3),(8,0)]
  | 76 => [(4,5),(7,3),(8,5)]
  | 77 => [(4,2),(7,0)]
  | 78 => [(0,4),(1,1),(6,1)]
  | 79 => [(5,1),(5,4)]
  | 80 => [(0,1),(6,4)]
  | 81 => [(1,2),(6,2)]
  | 82 => [(7,4),(8,4)]
  | 83 => [(0,0),(6,3),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5),(7,5),(8,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(2,1),(4,1),(7,1),(8,1)]
  | 89 => [(0,2),(1,5),(7,5)]
  | _ => [(0,3),(1,1),(6,1)]
def root8Node10Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1),(8,1)]
  | 7 => some [(1,5)]
  | 8 => some [(6,1)]
  | 9 => some [(5,1),(8,1)]
  | 10 => some [(0,1),(6,5)]
  | 11 => some [(0,4),(6,2)]
  | 12 => some [(5,4),(8,4)]
  | 13 => some [(5,0),(5,3)]
  | 14 => some [(4,5),(8,5)]
  | 15 => some [(7,0)]
  | 16 => some [(8,3)]
  | 17 => some [(8,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(3,4),(5,4),(7,4)]
  | 22 => some [(0,0),(6,3)]
  | 23 => some [(7,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(6,3),(7,3)]
  | 29 => some [(2,2),(4,2)]
  | 30 => some [(2,1),(2,3),(4,3)]
  | 31 => some [(0,2),(1,5)]
  | 32 => some [(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(5,1),(8,1)]
  | 37 => some [(0,1),(0,2),(6,5)]
  | 38 => some [(0,4),(1,1),(6,2)]
  | 39 => some [(0,1),(1,4),(3,4),(7,4)]
  | 40 => some [(0,0),(1,4),(6,4)]
  | 41 => some [(0,5),(1,2),(3,2)]
  | 42 => some [(2,0),(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(1,0),(3,0),(5,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => some [(0,3),(6,0),(6,1)]
  | 52 => some [(3,1),(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(6,4)]
  | 60 => some [(1,2),(3,2),(7,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,1)]
  | 70 => some [(0,0),(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0)]
  | 78 => some [(0,4),(1,1),(6,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4),(8,4)]
  | 83 => some [(0,0),(6,3),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5),(7,5),(8,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1),(7,1),(8,1)]
  | 89 => some [(0,2),(1,5),(7,5)]
  | _ => some [(0,3),(1,1),(6,1)]
theorem root8Node10Domains3_fast_eq : root8Node10Domains3 = expandDomains root8Node10Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node10Domains3 v = expandDomains root8Node10Domains3Fast v from by decide) v
theorem root8Node10Step3Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq (by decide)
theorem root8Node10Step3Narrowing_checked :
    checkNarrowing table13 root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkNarrowing_flatten table13Scope [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5]
    root8Node10Domains2 root8Node10Domains3 (by
      simp only [List.all_cons, List.all_nil, root8Node10Step3Chunk0_0_checked, root8Node10Step3Chunk0_1_checked, root8Node10Step3Chunk0_2_checked, root8Node10Step3Chunk0_3_checked, root8Node10Step3Chunk0_4_checked, root8Node10Step3Chunk0_5_checked, root8Node10Step3Chunk1_0_checked, root8Node10Step3Chunk1_1_checked, root8Node10Step3Chunk1_2_checked, root8Node10Step3Chunk1_3_checked, root8Node10Step3Chunk1_4_checked, root8Node10Step3Chunk1_5_checked, root8Node10Step3Chunk2_0_checked, root8Node10Step3Chunk2_1_checked, root8Node10Step3Chunk2_2_checked, root8Node10Step3Chunk2_3_checked, root8Node10Step3Chunk2_4_checked, root8Node10Step3Chunk2_5_checked, root8Node10Step3Chunk3_0_checked, root8Node10Step3Chunk3_1_checked, root8Node10Step3Chunk3_2_checked, root8Node10Step3Chunk3_3_checked, root8Node10Step3Chunk3_4_checked, root8Node10Step3Chunk3_5_checked, root8Node10Step3Chunk4_0_checked, root8Node10Step3Chunk4_1_checked, root8Node10Step3Chunk4_2_checked, root8Node10Step3Chunk4_3_checked, root8Node10Step3Chunk4_4_checked, root8Node10Step3Chunk4_5_checked, root8Node10Step3Chunk5_0_checked, root8Node10Step3Chunk5_1_checked, root8Node10Step3Chunk5_2_checked, root8Node10Step3Chunk5_3_checked, root8Node10Step3Chunk5_4_checked, root8Node10Step3Chunk5_5_checked, root8Node10Step3Chunk6_0_checked, root8Node10Step3Chunk6_1_checked, root8Node10Step3Chunk6_2_checked, root8Node10Step3Chunk6_3_checked, root8Node10Step3Chunk6_4_checked, root8Node10Step3Chunk6_5_checked, root8Node10Step3Chunk7_0_checked, root8Node10Step3Chunk7_1_checked, root8Node10Step3Chunk7_2_checked, root8Node10Step3Chunk7_3_checked, root8Node10Step3Chunk7_4_checked, root8Node10Step3Chunk7_5_checked, root8Node10Step3Chunk8_0_checked, root8Node10Step3Chunk8_1_checked, root8Node10Step3Chunk8_2_checked, root8Node10Step3Chunk8_3_checked, root8Node10Step3Chunk8_4_checked, root8Node10Step3Chunk8_5_checked, Bool.true_and])
theorem root8Node10Step3_checked :
    checkReplacement table13 root8Node10Domains2 root8Node10Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root8Node10Domains2 root8Node10Domains3
    root8Node10Domains2Fast root8Node10Domains3Fast
    root8Node10Domains2_fast_eq root8Node10Domains3_fast_eq
    root8Node10Step3Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
