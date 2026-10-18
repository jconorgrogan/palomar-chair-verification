module

public import SpectreFinite.RadiusFiveRoot6Part33
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveTable53
public import SpectreFinite.RadiusFiveTable55

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node81Domains0 : Domains 91 State := restrict root6Node80Domains1 3 (1,0)
def root6Node81Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(4,3),(7,1)]
  | 5 => some [(1,5),(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(7,4),(8,0)]
  | 11 => some [(1,3),(4,5),(7,3)]
  | 12 => some [(4,2),(7,0)]
  | 13 => some [(1,1),(6,1)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(6,5)]
  | 16 => some [(0,4),(1,1)]
  | 17 => some [(5,1),(5,4),(8,1)]
  | 18 => some [(0,0),(0,1),(6,4),(6,5)]
  | 19 => some [(0,4),(1,2),(6,2),(7,2)]
  | 20 => some [(1,4),(3,4),(7,4)]
  | 21 => some [(2,0),(4,0),(7,0),(8,0)]
  | 22 => some [(7,3),(8,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => some [(2,1),(2,3),(2,5),(4,1)]
  | 29 => some [(0,2),(6,0)]
  | 30 => some [(3,1),(4,4),(5,1),(5,4),(8,4)]
  | 31 => some [(0,1),(1,4)]
  | 32 => some [(0,5),(6,2)]
  | 33 => some [(4,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(6,4),(7,3)]
  | 38 => some [(1,2),(3,2),(5,2),(7,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => some [(4,5),(7,5),(8,5)]
  | 42 => some [(1,0),(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5),(7,5)]
  | 48 => some [(0,3),(0,4),(6,1),(6,2)]
  | 49 => some [(5,1),(5,4),(8,4)]
  | 50 => some [(0,1),(1,4),(6,4)]
  | 51 => some [(0,0),(1,3),(7,3)]
  | 52 => some [(7,2),(8,2)]
  | 53 => some [(4,0),(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(1,0),(4,2),(7,0)]
  | 59 => some [(4,3),(5,3),(7,1),(8,3)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(0,4),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(8,4)]
  | 63 => some [(0,1),(6,4)]
  | 64 => some [(1,2),(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0),(6,4)]
  | 67 => some [(1,2),(7,2)]
  | 68 => some [(4,0),(7,4)]
  | 69 => some [(1,3),(7,3)]
  | 70 => some [(4,3),(7,1),(8,3)]
  | 71 => some [(7,5),(8,5)]
  | 72 => some [(0,3),(1,0)]
  | 73 => some [(7,1),(8,1)]
  | 74 => some [(1,5),(7,5)]
  | 75 => some [(0,3),(6,1)]
  | 76 => some [(5,1),(8,1)]
  | 77 => some [(0,1),(6,5)]
  | 78 => some [(1,3),(6,3),(7,3)]
  | 79 => some [(4,2),(7,2),(8,2)]
  | 80 => some [(4,0),(5,0),(5,3),(8,0)]
  | 81 => some [(4,5),(5,5),(7,3),(8,5)]
  | 82 => some [(4,2),(7,0)]
  | 83 => some [(5,3),(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(1,1),(1,2),(6,2)]
  | 86 => some [(1,4),(3,4),(5,1),(5,4),(7,4)]
  | 87 => some [(0,0),(0,1),(0,5),(6,3),(6,4)]
  | 88 => some [(1,2),(4,4),(6,2),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root6Node81Domains0_fast_eq : root6Node81Domains0 = expandDomains root6Node81Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node81Domains0 v = expandDomains root6Node81Domains0Fast v from by decide) v
def root6Node81Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5),(7,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3),(6,3)]
  | 9 => [(7,2),(8,2)]
  | 10 => [(4,0),(5,0),(8,0)]
  | 11 => [(4,5),(7,3)]
  | 12 => [(4,2),(7,0)]
  | 13 => [(1,1),(6,1)]
  | 14 => [(4,1),(8,1)]
  | 15 => [(0,2),(6,5)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | 18 => [(0,0),(0,1),(6,4)]
  | 19 => [(1,2),(6,2),(7,2)]
  | 20 => [(7,4)]
  | 21 => [(2,0),(4,0),(7,0),(8,0)]
  | 22 => [(7,3),(8,3)]
  | 23 => [(5,2),(5,5)]
  | 24 => [(7,0),(8,0)]
  | 25 => [(4,3),(8,3)]
  | 26 => [(1,5),(3,5),(5,5)]
  | 27 => [(0,3),(1,0),(6,1)]
  | 28 => [(2,1),(4,1)]
  | 29 => [(0,2)]
  | 30 => [(3,1),(4,4),(5,1),(5,4),(8,4)]
  | 31 => [(0,1),(1,4)]
  | 32 => [(0,5),(6,2)]
  | 33 => [(4,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0),(2,4),(4,4)]
  | 37 => [(0,0),(1,3),(7,3)]
  | 38 => [(3,2),(5,2)]
  | 39 => [(4,0),(8,0)]
  | 40 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => [(4,5),(7,5),(8,5)]
  | 42 => [(1,0),(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1),(7,1)]
  | 47 => [(0,1),(1,5),(6,5)]
  | 48 => [(0,4),(6,1),(6,2)]
  | 49 => [(5,1),(5,4),(8,4)]
  | 50 => [(0,1),(1,4),(6,4)]
  | 51 => [(0,0),(1,3),(7,3)]
  | 52 => [(7,2),(8,2)]
  | 53 => [(4,0),(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0),(7,0)]
  | 59 => [(4,3),(7,1),(8,3)]
  | 60 => [(7,5),(8,5)]
  | 61 => [(0,4),(6,1),(6,2)]
  | 62 => [(5,1),(5,4),(8,4)]
  | 63 => [(0,1),(6,4)]
  | 64 => [(1,2),(6,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0),(7,4)]
  | 69 => [(1,3),(7,3)]
  | 70 => [(4,3),(7,1),(8,3)]
  | 71 => [(7,5),(8,5)]
  | 72 => [(0,3),(1,0)]
  | 73 => [(7,1),(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1),(8,1)]
  | 77 => [(0,1),(6,5)]
  | 78 => [(1,3),(6,3),(7,3)]
  | 79 => [(4,2),(7,2),(8,2)]
  | 80 => [(4,0),(5,0),(5,3),(8,0)]
  | 81 => [(4,5),(5,5),(7,3),(8,5)]
  | 82 => [(4,2),(7,0)]
  | 83 => [(5,3),(8,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(0,4),(1,1),(1,2),(6,2)]
  | 86 => [(1,4),(3,4),(5,1),(5,4),(7,4)]
  | 87 => [(0,0),(0,1),(0,5),(6,3),(6,4)]
  | 88 => [(1,2),(4,4),(6,2),(7,2)]
  | 89 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root6Node81Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5),(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(8,0)]
  | 11 => some [(4,5),(7,3)]
  | 12 => some [(4,2),(7,0)]
  | 13 => some [(1,1),(6,1)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(6,5)]
  | 16 => some [(0,4),(1,1)]
  | 17 => some [(5,1),(5,4)]
  | 18 => some [(0,0),(0,1),(6,4)]
  | 19 => some [(1,2),(6,2),(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,0),(4,0),(7,0),(8,0)]
  | 22 => some [(7,3),(8,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(6,1)]
  | 28 => some [(2,1),(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(3,1),(4,4),(5,1),(5,4),(8,4)]
  | 31 => some [(0,1),(1,4)]
  | 32 => some [(0,5),(6,2)]
  | 33 => some [(4,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(7,3)]
  | 38 => some [(3,2),(5,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => some [(4,5),(7,5),(8,5)]
  | 42 => some [(1,0),(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5)]
  | 48 => some [(0,4),(6,1),(6,2)]
  | 49 => some [(5,1),(5,4),(8,4)]
  | 50 => some [(0,1),(1,4),(6,4)]
  | 51 => some [(0,0),(1,3),(7,3)]
  | 52 => some [(7,2),(8,2)]
  | 53 => some [(4,0),(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0),(7,0)]
  | 59 => some [(4,3),(7,1),(8,3)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(0,4),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(8,4)]
  | 63 => some [(0,1),(6,4)]
  | 64 => some [(1,2),(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0),(7,4)]
  | 69 => some [(1,3),(7,3)]
  | 70 => some [(4,3),(7,1),(8,3)]
  | 71 => some [(7,5),(8,5)]
  | 72 => some [(0,3),(1,0)]
  | 73 => some [(7,1),(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1),(8,1)]
  | 77 => some [(0,1),(6,5)]
  | 78 => some [(1,3),(6,3),(7,3)]
  | 79 => some [(4,2),(7,2),(8,2)]
  | 80 => some [(4,0),(5,0),(5,3),(8,0)]
  | 81 => some [(4,5),(5,5),(7,3),(8,5)]
  | 82 => some [(4,2),(7,0)]
  | 83 => some [(5,3),(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(1,1),(1,2),(6,2)]
  | 86 => some [(1,4),(3,4),(5,1),(5,4),(7,4)]
  | 87 => some [(0,0),(0,1),(0,5),(6,3),(6,4)]
  | 88 => some [(1,2),(4,4),(6,2),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root6Node81Domains1_fast_eq : root6Node81Domains1 = expandDomains root6Node81Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node81Domains1 v = expandDomains root6Node81Domains1Fast v from by decide) v
theorem root6Node81Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq (by decide)
theorem root6Node81Step1Narrowing_checked :
    checkNarrowing table35 root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkNarrowing_flatten table35Scope [table35Rows0_0,table35Rows0_1,table35Rows0_2,table35Rows0_3,table35Rows0_4,table35Rows0_5,table35Rows1_0,table35Rows1_1,table35Rows1_2,table35Rows1_3,table35Rows1_4,table35Rows1_5,table35Rows2_0,table35Rows2_1,table35Rows2_2,table35Rows2_3,table35Rows2_4,table35Rows2_5,table35Rows3_0,table35Rows3_1,table35Rows3_2,table35Rows3_3,table35Rows3_4,table35Rows3_5,table35Rows4_0,table35Rows4_1,table35Rows4_2,table35Rows4_3,table35Rows4_4,table35Rows4_5,table35Rows5_0,table35Rows5_1,table35Rows5_2,table35Rows5_3,table35Rows5_4,table35Rows5_5,table35Rows6_0,table35Rows6_1,table35Rows6_2,table35Rows6_3,table35Rows6_4,table35Rows6_5,table35Rows7_0,table35Rows7_1,table35Rows7_2,table35Rows7_3,table35Rows7_4,table35Rows7_5,table35Rows8_0,table35Rows8_1,table35Rows8_2,table35Rows8_3,table35Rows8_4,table35Rows8_5]
    root6Node81Domains0 root6Node81Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node81Step1Chunk0_0_checked, root6Node81Step1Chunk0_1_checked, root6Node81Step1Chunk0_2_checked, root6Node81Step1Chunk0_3_checked, root6Node81Step1Chunk0_4_checked, root6Node81Step1Chunk0_5_checked, root6Node81Step1Chunk1_0_checked, root6Node81Step1Chunk1_1_checked, root6Node81Step1Chunk1_2_checked, root6Node81Step1Chunk1_3_checked, root6Node81Step1Chunk1_4_checked, root6Node81Step1Chunk1_5_checked, root6Node81Step1Chunk2_0_checked, root6Node81Step1Chunk2_1_checked, root6Node81Step1Chunk2_2_checked, root6Node81Step1Chunk2_3_checked, root6Node81Step1Chunk2_4_checked, root6Node81Step1Chunk2_5_checked, root6Node81Step1Chunk3_0_checked, root6Node81Step1Chunk3_1_checked, root6Node81Step1Chunk3_2_checked, root6Node81Step1Chunk3_3_checked, root6Node81Step1Chunk3_4_checked, root6Node81Step1Chunk3_5_checked, root6Node81Step1Chunk4_0_checked, root6Node81Step1Chunk4_1_checked, root6Node81Step1Chunk4_2_checked, root6Node81Step1Chunk4_3_checked, root6Node81Step1Chunk4_4_checked, root6Node81Step1Chunk4_5_checked, root6Node81Step1Chunk5_0_checked, root6Node81Step1Chunk5_1_checked, root6Node81Step1Chunk5_2_checked, root6Node81Step1Chunk5_3_checked, root6Node81Step1Chunk5_4_checked, root6Node81Step1Chunk5_5_checked, root6Node81Step1Chunk6_0_checked, root6Node81Step1Chunk6_1_checked, root6Node81Step1Chunk6_2_checked, root6Node81Step1Chunk6_3_checked, root6Node81Step1Chunk6_4_checked, root6Node81Step1Chunk6_5_checked, root6Node81Step1Chunk7_0_checked, root6Node81Step1Chunk7_1_checked, root6Node81Step1Chunk7_2_checked, root6Node81Step1Chunk7_3_checked, root6Node81Step1Chunk7_4_checked, root6Node81Step1Chunk7_5_checked, root6Node81Step1Chunk8_0_checked, root6Node81Step1Chunk8_1_checked, root6Node81Step1Chunk8_2_checked, root6Node81Step1Chunk8_3_checked, root6Node81Step1Chunk8_4_checked, root6Node81Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node81Step1_checked :
    checkReplacement table35 root6Node81Domains0 root6Node81Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node81Domains0 root6Node81Domains1
    root6Node81Domains0Fast root6Node81Domains1Fast
    root6Node81Domains0_fast_eq root6Node81Domains1_fast_eq
    root6Node81Step1Narrowing_checked (by decide)
def root6Node81Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5),(7,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3),(6,3)]
  | 9 => [(7,2),(8,2)]
  | 10 => [(4,0),(5,0),(8,0)]
  | 11 => [(4,5),(7,3)]
  | 12 => [(4,2),(7,0)]
  | 13 => [(1,1),(6,1)]
  | 14 => [(4,1),(8,1)]
  | 15 => [(0,2),(6,5)]
  | 16 => [(0,4),(1,1)]
  | 17 => [(5,1),(5,4)]
  | 18 => [(0,0),(0,1),(6,4)]
  | 19 => [(1,2),(6,2),(7,2)]
  | 20 => [(7,4)]
  | 21 => [(2,0),(4,0),(7,0),(8,0)]
  | 22 => [(7,3),(8,3)]
  | 23 => [(5,2),(5,5)]
  | 24 => [(7,0),(8,0)]
  | 25 => [(4,3),(8,3)]
  | 26 => [(1,5),(3,5),(5,5)]
  | 27 => [(0,3),(1,0),(6,1)]
  | 28 => [(2,1),(4,1)]
  | 29 => [(0,2)]
  | 30 => [(3,1),(4,4),(5,1),(5,4),(8,4)]
  | 31 => [(0,1),(1,4)]
  | 32 => [(0,5),(6,2)]
  | 33 => [(4,4),(8,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0),(2,4),(4,4)]
  | 37 => [(0,0),(1,3),(7,3)]
  | 38 => [(3,2),(5,2)]
  | 39 => [(4,0),(8,0)]
  | 40 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => [(4,5),(7,5),(8,5)]
  | 42 => [(1,0),(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1),(7,1)]
  | 47 => [(0,1),(1,5),(6,5)]
  | 48 => [(0,4),(6,1),(6,2)]
  | 49 => [(5,1),(5,4),(8,4)]
  | 50 => [(0,1),(1,4),(6,4)]
  | 51 => [(0,0),(1,3),(7,3)]
  | 52 => [(7,2),(8,2)]
  | 53 => [(4,0),(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0),(7,0)]
  | 59 => [(4,3),(7,1),(8,3)]
  | 60 => [(7,5),(8,5)]
  | 61 => [(0,4),(6,1),(6,2)]
  | 62 => [(5,1),(5,4),(8,4)]
  | 63 => [(0,1),(6,4)]
  | 64 => [(1,2),(6,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0),(7,4)]
  | 69 => [(1,3),(7,3)]
  | 70 => [(4,3),(7,1),(8,3)]
  | 71 => [(7,5),(8,5)]
  | 72 => [(0,3),(1,0)]
  | 73 => [(7,1),(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1),(8,1)]
  | 77 => [(0,1),(6,5)]
  | 78 => [(1,3),(7,3)]
  | 79 => [(4,2),(8,2)]
  | 80 => [(5,0),(5,3)]
  | 81 => [(4,5),(5,5),(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(0,4),(1,2),(6,2)]
  | 86 => [(1,4),(3,4),(5,4),(7,4)]
  | 87 => [(0,0),(0,5),(6,3)]
  | 88 => [(4,4),(7,2)]
  | 89 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root6Node81Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5),(7,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(8,0)]
  | 11 => some [(4,5),(7,3)]
  | 12 => some [(4,2),(7,0)]
  | 13 => some [(1,1),(6,1)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(6,5)]
  | 16 => some [(0,4),(1,1)]
  | 17 => some [(5,1),(5,4)]
  | 18 => some [(0,0),(0,1),(6,4)]
  | 19 => some [(1,2),(6,2),(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,0),(4,0),(7,0),(8,0)]
  | 22 => some [(7,3),(8,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(6,1)]
  | 28 => some [(2,1),(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(3,1),(4,4),(5,1),(5,4),(8,4)]
  | 31 => some [(0,1),(1,4)]
  | 32 => some [(0,5),(6,2)]
  | 33 => some [(4,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(7,3)]
  | 38 => some [(3,2),(5,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => some [(4,5),(7,5),(8,5)]
  | 42 => some [(1,0),(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5)]
  | 48 => some [(0,4),(6,1),(6,2)]
  | 49 => some [(5,1),(5,4),(8,4)]
  | 50 => some [(0,1),(1,4),(6,4)]
  | 51 => some [(0,0),(1,3),(7,3)]
  | 52 => some [(7,2),(8,2)]
  | 53 => some [(4,0),(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0),(7,0)]
  | 59 => some [(4,3),(7,1),(8,3)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(0,4),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(8,4)]
  | 63 => some [(0,1),(6,4)]
  | 64 => some [(1,2),(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0),(7,4)]
  | 69 => some [(1,3),(7,3)]
  | 70 => some [(4,3),(7,1),(8,3)]
  | 71 => some [(7,5),(8,5)]
  | 72 => some [(0,3),(1,0)]
  | 73 => some [(7,1),(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1),(8,1)]
  | 77 => some [(0,1),(6,5)]
  | 78 => some [(1,3),(7,3)]
  | 79 => some [(4,2),(8,2)]
  | 80 => some [(5,0),(5,3)]
  | 81 => some [(4,5),(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(1,2),(6,2)]
  | 86 => some [(1,4),(3,4),(5,4),(7,4)]
  | 87 => some [(0,0),(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root6Node81Domains2_fast_eq : root6Node81Domains2 = expandDomains root6Node81Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node81Domains2 v = expandDomains root6Node81Domains2Fast v from by decide) v
theorem root6Node81Step2Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq (by decide)
theorem root6Node81Step2Narrowing_checked :
    checkNarrowing table55 root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root6Node81Domains1 root6Node81Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node81Step2Chunk0_0_checked, root6Node81Step2Chunk0_1_checked, root6Node81Step2Chunk0_2_checked, root6Node81Step2Chunk0_3_checked, root6Node81Step2Chunk0_4_checked, root6Node81Step2Chunk0_5_checked, root6Node81Step2Chunk1_0_checked, root6Node81Step2Chunk1_1_checked, root6Node81Step2Chunk1_2_checked, root6Node81Step2Chunk1_3_checked, root6Node81Step2Chunk1_4_checked, root6Node81Step2Chunk1_5_checked, root6Node81Step2Chunk2_0_checked, root6Node81Step2Chunk2_1_checked, root6Node81Step2Chunk2_2_checked, root6Node81Step2Chunk2_3_checked, root6Node81Step2Chunk2_4_checked, root6Node81Step2Chunk2_5_checked, root6Node81Step2Chunk3_0_checked, root6Node81Step2Chunk3_1_checked, root6Node81Step2Chunk3_2_checked, root6Node81Step2Chunk3_3_checked, root6Node81Step2Chunk3_4_checked, root6Node81Step2Chunk3_5_checked, root6Node81Step2Chunk4_0_checked, root6Node81Step2Chunk4_1_checked, root6Node81Step2Chunk4_2_checked, root6Node81Step2Chunk4_3_checked, root6Node81Step2Chunk4_4_checked, root6Node81Step2Chunk4_5_checked, root6Node81Step2Chunk5_0_checked, root6Node81Step2Chunk5_1_checked, root6Node81Step2Chunk5_2_checked, root6Node81Step2Chunk5_3_checked, root6Node81Step2Chunk5_4_checked, root6Node81Step2Chunk5_5_checked, root6Node81Step2Chunk6_0_checked, root6Node81Step2Chunk6_1_checked, root6Node81Step2Chunk6_2_checked, root6Node81Step2Chunk6_3_checked, root6Node81Step2Chunk6_4_checked, root6Node81Step2Chunk6_5_checked, root6Node81Step2Chunk7_0_checked, root6Node81Step2Chunk7_1_checked, root6Node81Step2Chunk7_2_checked, root6Node81Step2Chunk7_3_checked, root6Node81Step2Chunk7_4_checked, root6Node81Step2Chunk7_5_checked, root6Node81Step2Chunk8_0_checked, root6Node81Step2Chunk8_1_checked, root6Node81Step2Chunk8_2_checked, root6Node81Step2Chunk8_3_checked, root6Node81Step2Chunk8_4_checked, root6Node81Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node81Step2_checked :
    checkReplacement table55 root6Node81Domains1 root6Node81Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node81Domains1 root6Node81Domains2
    root6Node81Domains1Fast root6Node81Domains2Fast
    root6Node81Domains1_fast_eq root6Node81Domains2_fast_eq
    root6Node81Step2Narrowing_checked (by decide)
def root6Node82Domains0 : Domains 91 State := restrict root6Node81Domains2 5 (1,5)
def root6Node82Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3),(6,3)]
  | 9 => some [(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(8,0)]
  | 11 => some [(4,5),(7,3)]
  | 12 => some [(4,2),(7,0)]
  | 13 => some [(1,1),(6,1)]
  | 14 => some [(4,1),(8,1)]
  | 15 => some [(0,2),(6,5)]
  | 16 => some [(0,4),(1,1)]
  | 17 => some [(5,1),(5,4)]
  | 18 => some [(0,0),(0,1),(6,4)]
  | 19 => some [(1,2),(6,2),(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,0),(4,0),(7,0),(8,0)]
  | 22 => some [(7,3),(8,3)]
  | 23 => some [(5,2),(5,5)]
  | 24 => some [(7,0),(8,0)]
  | 25 => some [(4,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(6,1)]
  | 28 => some [(2,1),(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(3,1),(4,4),(5,1),(5,4),(8,4)]
  | 31 => some [(0,1),(1,4)]
  | 32 => some [(0,5),(6,2)]
  | 33 => some [(4,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(7,3)]
  | 38 => some [(3,2),(5,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => some [(4,5),(7,5),(8,5)]
  | 42 => some [(1,0),(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5)]
  | 48 => some [(0,4),(6,1),(6,2)]
  | 49 => some [(5,1),(5,4),(8,4)]
  | 50 => some [(0,1),(1,4),(6,4)]
  | 51 => some [(0,0),(1,3),(7,3)]
  | 52 => some [(7,2),(8,2)]
  | 53 => some [(4,0),(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0),(7,0)]
  | 59 => some [(4,3),(7,1),(8,3)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(0,4),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(8,4)]
  | 63 => some [(0,1),(6,4)]
  | 64 => some [(1,2),(6,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0),(7,4)]
  | 69 => some [(1,3),(7,3)]
  | 70 => some [(4,3),(7,1),(8,3)]
  | 71 => some [(7,5),(8,5)]
  | 72 => some [(0,3),(1,0)]
  | 73 => some [(7,1),(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1),(8,1)]
  | 77 => some [(0,1),(6,5)]
  | 78 => some [(1,3),(7,3)]
  | 79 => some [(4,2),(8,2)]
  | 80 => some [(5,0),(5,3)]
  | 81 => some [(4,5),(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(1,2),(6,2)]
  | 86 => some [(1,4),(3,4),(5,4),(7,4)]
  | 87 => some [(0,0),(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root6Node82Domains0_fast_eq : root6Node82Domains0 = expandDomains root6Node82Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node82Domains0 v = expandDomains root6Node82Domains0Fast v from by decide) v
def root6Node82Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(1,1),(6,1)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(2,0),(4,0),(7,0),(8,0)]
  | 22 => [(8,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(3,1),(4,4),(5,1),(5,4),(8,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0)]
  | 37 => [(7,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => [(4,5),(7,5),(8,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(0,1),(1,4),(6,4)]
  | 51 => [(0,0),(1,3),(7,3)]
  | 52 => [(7,2),(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0)]
  | 59 => [(7,1)]
  | 60 => [(7,5),(8,5)]
  | 61 => [(0,4),(6,1),(6,2)]
  | 62 => [(5,1),(5,4),(8,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0)]
  | 69 => [(1,3),(7,3)]
  | 70 => [(4,3),(7,1),(8,3)]
  | 71 => [(7,5),(8,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1)]
  | 77 => [(0,1),(6,5)]
  | 78 => [(1,3),(7,3)]
  | 79 => [(4,2),(8,2)]
  | 80 => [(5,0),(5,3)]
  | 81 => [(4,5),(5,5),(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(0,4),(1,2),(6,2)]
  | 86 => [(1,4),(3,4),(5,4),(7,4)]
  | 87 => [(0,0),(0,5),(6,3)]
  | 88 => [(4,4),(7,2)]
  | 89 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root6Node82Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(1,1),(6,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(2,0),(4,0),(7,0),(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(3,1),(4,4),(5,1),(5,4),(8,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 41 => some [(4,5),(7,5),(8,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(0,1),(1,4),(6,4)]
  | 51 => some [(0,0),(1,3),(7,3)]
  | 52 => some [(7,2),(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(0,4),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(1,3),(7,3)]
  | 70 => some [(4,3),(7,1),(8,3)]
  | 71 => some [(7,5),(8,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1),(6,5)]
  | 78 => some [(1,3),(7,3)]
  | 79 => some [(4,2),(8,2)]
  | 80 => some [(5,0),(5,3)]
  | 81 => some [(4,5),(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(1,2),(6,2)]
  | 86 => some [(1,4),(3,4),(5,4),(7,4)]
  | 87 => some [(0,0),(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root6Node82Domains1_fast_eq : root6Node82Domains1 = expandDomains root6Node82Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node82Domains1 v = expandDomains root6Node82Domains1Fast v from by decide) v
theorem root6Node82Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq (by decide)
theorem root6Node82Step1Narrowing_checked :
    checkNarrowing table35 root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkNarrowing_flatten table35Scope [table35Rows0_0,table35Rows0_1,table35Rows0_2,table35Rows0_3,table35Rows0_4,table35Rows0_5,table35Rows1_0,table35Rows1_1,table35Rows1_2,table35Rows1_3,table35Rows1_4,table35Rows1_5,table35Rows2_0,table35Rows2_1,table35Rows2_2,table35Rows2_3,table35Rows2_4,table35Rows2_5,table35Rows3_0,table35Rows3_1,table35Rows3_2,table35Rows3_3,table35Rows3_4,table35Rows3_5,table35Rows4_0,table35Rows4_1,table35Rows4_2,table35Rows4_3,table35Rows4_4,table35Rows4_5,table35Rows5_0,table35Rows5_1,table35Rows5_2,table35Rows5_3,table35Rows5_4,table35Rows5_5,table35Rows6_0,table35Rows6_1,table35Rows6_2,table35Rows6_3,table35Rows6_4,table35Rows6_5,table35Rows7_0,table35Rows7_1,table35Rows7_2,table35Rows7_3,table35Rows7_4,table35Rows7_5,table35Rows8_0,table35Rows8_1,table35Rows8_2,table35Rows8_3,table35Rows8_4,table35Rows8_5]
    root6Node82Domains0 root6Node82Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node82Step1Chunk0_0_checked, root6Node82Step1Chunk0_1_checked, root6Node82Step1Chunk0_2_checked, root6Node82Step1Chunk0_3_checked, root6Node82Step1Chunk0_4_checked, root6Node82Step1Chunk0_5_checked, root6Node82Step1Chunk1_0_checked, root6Node82Step1Chunk1_1_checked, root6Node82Step1Chunk1_2_checked, root6Node82Step1Chunk1_3_checked, root6Node82Step1Chunk1_4_checked, root6Node82Step1Chunk1_5_checked, root6Node82Step1Chunk2_0_checked, root6Node82Step1Chunk2_1_checked, root6Node82Step1Chunk2_2_checked, root6Node82Step1Chunk2_3_checked, root6Node82Step1Chunk2_4_checked, root6Node82Step1Chunk2_5_checked, root6Node82Step1Chunk3_0_checked, root6Node82Step1Chunk3_1_checked, root6Node82Step1Chunk3_2_checked, root6Node82Step1Chunk3_3_checked, root6Node82Step1Chunk3_4_checked, root6Node82Step1Chunk3_5_checked, root6Node82Step1Chunk4_0_checked, root6Node82Step1Chunk4_1_checked, root6Node82Step1Chunk4_2_checked, root6Node82Step1Chunk4_3_checked, root6Node82Step1Chunk4_4_checked, root6Node82Step1Chunk4_5_checked, root6Node82Step1Chunk5_0_checked, root6Node82Step1Chunk5_1_checked, root6Node82Step1Chunk5_2_checked, root6Node82Step1Chunk5_3_checked, root6Node82Step1Chunk5_4_checked, root6Node82Step1Chunk5_5_checked, root6Node82Step1Chunk6_0_checked, root6Node82Step1Chunk6_1_checked, root6Node82Step1Chunk6_2_checked, root6Node82Step1Chunk6_3_checked, root6Node82Step1Chunk6_4_checked, root6Node82Step1Chunk6_5_checked, root6Node82Step1Chunk7_0_checked, root6Node82Step1Chunk7_1_checked, root6Node82Step1Chunk7_2_checked, root6Node82Step1Chunk7_3_checked, root6Node82Step1Chunk7_4_checked, root6Node82Step1Chunk7_5_checked, root6Node82Step1Chunk8_0_checked, root6Node82Step1Chunk8_1_checked, root6Node82Step1Chunk8_2_checked, root6Node82Step1Chunk8_3_checked, root6Node82Step1Chunk8_4_checked, root6Node82Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node82Step1_checked :
    checkReplacement table35 root6Node82Domains0 root6Node82Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node82Domains0 root6Node82Domains1
    root6Node82Domains0Fast root6Node82Domains1Fast
    root6Node82Domains0_fast_eq root6Node82Domains1_fast_eq
    root6Node82Step1Narrowing_checked (by decide)
def root6Node82Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(8,3)]
  | 2 => [(8,5)]
  | 3 => [(1,0)]
  | 4 => [(7,1)]
  | 5 => [(1,5)]
  | 6 => [(7,2)]
  | 7 => [(7,4)]
  | 8 => [(1,3)]
  | 9 => [(8,2)]
  | 10 => [(5,0)]
  | 11 => [(4,5)]
  | 12 => [(7,0)]
  | 13 => [(1,1),(6,1)]
  | 14 => [(8,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(7,0),(8,0)]
  | 22 => [(8,3)]
  | 23 => [(5,5)]
  | 24 => [(7,0)]
  | 25 => [(4,3)]
  | 26 => [(1,5)]
  | 27 => [(6,1)]
  | 28 => [(4,1)]
  | 29 => [(0,2)]
  | 30 => [(4,4),(5,4),(8,4)]
  | 31 => [(1,4)]
  | 32 => [(0,5)]
  | 33 => [(4,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(2,0)]
  | 37 => [(7,3)]
  | 38 => [(5,2)]
  | 39 => [(8,0)]
  | 40 => [(4,3),(7,1)]
  | 41 => [(7,5)]
  | 42 => [(6,0)]
  | 43 => [(7,1)]
  | 44 => [(7,5)]
  | 45 => [(6,0)]
  | 46 => [(3,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(0,1),(1,4),(6,4)]
  | 51 => [(1,3),(7,3)]
  | 52 => [(8,2)]
  | 53 => [(8,0)]
  | 54 => [(7,3)]
  | 55 => [(8,2)]
  | 56 => [(5,0)]
  | 57 => [(4,5)]
  | 58 => [(1,0)]
  | 59 => [(7,1)]
  | 60 => [(7,5),(8,5)]
  | 61 => [(0,4),(6,2)]
  | 62 => [(5,4),(8,4)]
  | 63 => [(6,4)]
  | 64 => [(1,2)]
  | 65 => [(8,4)]
  | 66 => [(0,0)]
  | 67 => [(7,2)]
  | 68 => [(4,0)]
  | 69 => [(1,3),(7,3)]
  | 70 => [(4,3),(7,1)]
  | 71 => [(7,5)]
  | 72 => [(0,3)]
  | 73 => [(8,1)]
  | 74 => [(1,5)]
  | 75 => [(6,1)]
  | 76 => [(5,1)]
  | 77 => [(0,1),(6,5)]
  | 78 => [(1,3),(7,3)]
  | 79 => [(4,2)]
  | 80 => [(5,3)]
  | 81 => [(5,5),(8,5)]
  | 82 => [(7,0)]
  | 83 => [(8,3)]
  | 84 => [(5,5),(8,5)]
  | 85 => [(0,4),(1,2),(6,2)]
  | 86 => [(1,4),(3,4),(7,4)]
  | 87 => [(0,5),(6,3)]
  | 88 => [(4,4),(7,2)]
  | 89 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root6Node82Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(8,3)]
  | 2 => some [(8,5)]
  | 3 => some [(1,0)]
  | 4 => some [(7,1)]
  | 5 => some [(1,5)]
  | 6 => some [(7,2)]
  | 7 => some [(7,4)]
  | 8 => some [(1,3)]
  | 9 => some [(8,2)]
  | 10 => some [(5,0)]
  | 11 => some [(4,5)]
  | 12 => some [(7,0)]
  | 13 => some [(1,1),(6,1)]
  | 14 => some [(8,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(7,0),(8,0)]
  | 22 => some [(8,3)]
  | 23 => some [(5,5)]
  | 24 => some [(7,0)]
  | 25 => some [(4,3)]
  | 26 => some [(1,5)]
  | 27 => some [(6,1)]
  | 28 => some [(4,1)]
  | 29 => some [(0,2)]
  | 30 => some [(4,4),(5,4),(8,4)]
  | 31 => some [(1,4)]
  | 32 => some [(0,5)]
  | 33 => some [(4,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0)]
  | 37 => some [(7,3)]
  | 38 => some [(5,2)]
  | 39 => some [(8,0)]
  | 40 => some [(4,3),(7,1)]
  | 41 => some [(7,5)]
  | 42 => some [(6,0)]
  | 43 => some [(7,1)]
  | 44 => some [(7,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(0,1),(1,4),(6,4)]
  | 51 => some [(1,3),(7,3)]
  | 52 => some [(8,2)]
  | 53 => some [(8,0)]
  | 54 => some [(7,3)]
  | 55 => some [(8,2)]
  | 56 => some [(5,0)]
  | 57 => some [(4,5)]
  | 58 => some [(1,0)]
  | 59 => some [(7,1)]
  | 60 => some [(7,5),(8,5)]
  | 61 => some [(0,4),(6,2)]
  | 62 => some [(5,4),(8,4)]
  | 63 => some [(6,4)]
  | 64 => some [(1,2)]
  | 65 => some [(8,4)]
  | 66 => some [(0,0)]
  | 67 => some [(7,2)]
  | 68 => some [(4,0)]
  | 69 => some [(1,3),(7,3)]
  | 70 => some [(4,3),(7,1)]
  | 71 => some [(7,5)]
  | 72 => some [(0,3)]
  | 73 => some [(8,1)]
  | 74 => some [(1,5)]
  | 75 => some [(6,1)]
  | 76 => some [(5,1)]
  | 77 => some [(0,1),(6,5)]
  | 78 => some [(1,3),(7,3)]
  | 79 => some [(4,2)]
  | 80 => some [(5,3)]
  | 81 => some [(5,5),(8,5)]
  | 82 => some [(7,0)]
  | 83 => some [(8,3)]
  | 84 => some [(5,5),(8,5)]
  | 85 => some [(0,4),(1,2),(6,2)]
  | 86 => some [(1,4),(3,4),(7,4)]
  | 87 => some [(0,5),(6,3)]
  | 88 => some [(4,4),(7,2)]
  | 89 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root6Node82Domains2_fast_eq : root6Node82Domains2 = expandDomains root6Node82Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node82Domains2 v = expandDomains root6Node82Domains2Fast v from by decide) v
theorem root6Node82Step2Chunk0_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_0⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk0_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_1⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk0_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_2⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk0_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_3⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk0_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_4⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk0_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows0_5⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk1_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_0⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk1_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_1⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk1_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_2⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk1_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_3⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk1_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_4⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk1_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows1_5⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk2_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_0⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk2_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_1⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk2_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_2⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk2_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_3⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk2_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_4⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk2_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows2_5⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk3_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_0⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk3_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_1⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk3_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_2⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk3_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_3⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk3_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_4⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk3_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows3_5⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk4_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_0⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk4_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_1⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk4_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_2⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk4_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_3⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk4_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_4⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk4_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows4_5⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk5_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_0⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk5_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_1⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk5_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_2⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk5_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_3⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk5_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_4⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk5_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows5_5⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk6_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_0⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk6_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_1⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk6_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_2⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk6_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_3⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk6_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_4⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk6_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows6_5⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk7_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_0⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk7_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_1⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk7_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_2⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk7_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_3⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk7_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_4⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk7_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows7_5⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk8_0_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_0⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk8_1_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_1⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk8_2_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_2⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk8_3_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_3⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk8_4_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_4⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Chunk8_5_checked :
    checkNarrowing ⟨table53Scope, table53Rows8_5⟩
      root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq (by decide)
theorem root6Node82Step2Narrowing_checked :
    checkNarrowing table53 root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkNarrowing_flatten table53Scope [table53Rows0_0,table53Rows0_1,table53Rows0_2,table53Rows0_3,table53Rows0_4,table53Rows0_5,table53Rows1_0,table53Rows1_1,table53Rows1_2,table53Rows1_3,table53Rows1_4,table53Rows1_5,table53Rows2_0,table53Rows2_1,table53Rows2_2,table53Rows2_3,table53Rows2_4,table53Rows2_5,table53Rows3_0,table53Rows3_1,table53Rows3_2,table53Rows3_3,table53Rows3_4,table53Rows3_5,table53Rows4_0,table53Rows4_1,table53Rows4_2,table53Rows4_3,table53Rows4_4,table53Rows4_5,table53Rows5_0,table53Rows5_1,table53Rows5_2,table53Rows5_3,table53Rows5_4,table53Rows5_5,table53Rows6_0,table53Rows6_1,table53Rows6_2,table53Rows6_3,table53Rows6_4,table53Rows6_5,table53Rows7_0,table53Rows7_1,table53Rows7_2,table53Rows7_3,table53Rows7_4,table53Rows7_5,table53Rows8_0,table53Rows8_1,table53Rows8_2,table53Rows8_3,table53Rows8_4,table53Rows8_5]
    root6Node82Domains1 root6Node82Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node82Step2Chunk0_0_checked, root6Node82Step2Chunk0_1_checked, root6Node82Step2Chunk0_2_checked, root6Node82Step2Chunk0_3_checked, root6Node82Step2Chunk0_4_checked, root6Node82Step2Chunk0_5_checked, root6Node82Step2Chunk1_0_checked, root6Node82Step2Chunk1_1_checked, root6Node82Step2Chunk1_2_checked, root6Node82Step2Chunk1_3_checked, root6Node82Step2Chunk1_4_checked, root6Node82Step2Chunk1_5_checked, root6Node82Step2Chunk2_0_checked, root6Node82Step2Chunk2_1_checked, root6Node82Step2Chunk2_2_checked, root6Node82Step2Chunk2_3_checked, root6Node82Step2Chunk2_4_checked, root6Node82Step2Chunk2_5_checked, root6Node82Step2Chunk3_0_checked, root6Node82Step2Chunk3_1_checked, root6Node82Step2Chunk3_2_checked, root6Node82Step2Chunk3_3_checked, root6Node82Step2Chunk3_4_checked, root6Node82Step2Chunk3_5_checked, root6Node82Step2Chunk4_0_checked, root6Node82Step2Chunk4_1_checked, root6Node82Step2Chunk4_2_checked, root6Node82Step2Chunk4_3_checked, root6Node82Step2Chunk4_4_checked, root6Node82Step2Chunk4_5_checked, root6Node82Step2Chunk5_0_checked, root6Node82Step2Chunk5_1_checked, root6Node82Step2Chunk5_2_checked, root6Node82Step2Chunk5_3_checked, root6Node82Step2Chunk5_4_checked, root6Node82Step2Chunk5_5_checked, root6Node82Step2Chunk6_0_checked, root6Node82Step2Chunk6_1_checked, root6Node82Step2Chunk6_2_checked, root6Node82Step2Chunk6_3_checked, root6Node82Step2Chunk6_4_checked, root6Node82Step2Chunk6_5_checked, root6Node82Step2Chunk7_0_checked, root6Node82Step2Chunk7_1_checked, root6Node82Step2Chunk7_2_checked, root6Node82Step2Chunk7_3_checked, root6Node82Step2Chunk7_4_checked, root6Node82Step2Chunk7_5_checked, root6Node82Step2Chunk8_0_checked, root6Node82Step2Chunk8_1_checked, root6Node82Step2Chunk8_2_checked, root6Node82Step2Chunk8_3_checked, root6Node82Step2Chunk8_4_checked, root6Node82Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node82Step2_checked :
    checkReplacement table53 root6Node82Domains1 root6Node82Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node82Domains1 root6Node82Domains2
    root6Node82Domains1Fast root6Node82Domains2Fast
    root6Node82Domains1_fast_eq root6Node82Domains2_fast_eq
    root6Node82Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
