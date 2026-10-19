module

public import SpectreFinite.RadiusFiveRoot7Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable0
public import SpectreFinite.RadiusFiveTable19
public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node81Domains0 : Domains 91 State := restrict root7Node1Domains4 14 (8,3)
def root7Node81Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(7,2),(8,4)]
  | 1 => some [(1,4),(4,0),(7,4)]
  | 2 => some [(0,5),(1,3),(6,3),(7,3)]
  | 3 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 4 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 5 => some [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => some [(1,1),(6,1),(7,1)]
  | 7 => some [(4,1),(5,1),(7,5),(8,1)]
  | 8 => some [(0,1),(0,2),(6,0),(6,5)]
  | 9 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 10 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 11 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(4,0),(7,0),(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,2),(5,5),(8,2)]
  | 16 => some [(1,0),(3,0),(5,0)]
  | 17 => some [(2,1),(2,5),(4,5)]
  | 18 => some [(0,2),(1,0),(6,0),(7,0)]
  | 19 => some [(1,1),(4,3),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(4,4),(5,1),(5,4),(8,4)]
  | 22 => some [(0,1),(1,4),(6,4)]
  | 23 => some [(0,5),(1,2),(6,2)]
  | 24 => some [(4,4),(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2),(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(4,2),(5,2),(8,2)]
  | 30 => some [(4,3),(5,3),(7,1),(8,3)]
  | 31 => some [(7,5),(8,5)]
  | 32 => some [(0,3),(1,0),(6,0)]
  | 33 => some [(7,1),(8,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1),(8,1)]
  | 37 => some [(0,1),(6,5)]
  | 38 => some [(0,4),(6,2)]
  | 39 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => some [(4,0),(7,4),(8,0)]
  | 41 => some [(1,3),(7,3)]
  | 42 => some [(4,2),(8,2)]
  | 43 => some [(5,0),(5,3)]
  | 44 => some [(4,5),(5,5),(8,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5),(8,5)]
  | 48 => some [(1,0),(3,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => some [(0,1),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(6,2)]
  | 53 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => some [(0,3),(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4)]
  | 71 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 72 => some [(2,0),(4,0),(7,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2),(8,5)]
  | 75 => some [(5,0),(7,0),(8,0)]
  | 76 => some [(4,3),(4,5),(7,3),(8,3)]
  | 77 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(7,5),(8,2)]
  | 78 => some [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => some [(0,1),(1,4),(7,4)]
  | 81 => some [(0,5),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(8,4)]
  | 83 => some [(0,0),(1,4),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(1,0),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(1,5),(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(6,0),(6,1),(6,5)]
theorem root7Node81Domains0_fast_eq : root7Node81Domains0 = expandDomains root7Node81Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node81Domains0 v = expandDomains root7Node81Domains0Fast v from by decide) v
def root7Node81Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(7,2),(8,4)]
  | 1 => [(4,0),(7,4)]
  | 2 => [(1,3),(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(5,5),(8,5)]
  | 6 => [(1,1),(6,1),(7,1)]
  | 7 => [(5,1),(8,1)]
  | 8 => [(0,1),(6,5)]
  | 9 => [(0,4),(6,2)]
  | 10 => [(1,4),(7,4)]
  | 11 => [(0,5),(6,3)]
  | 12 => [(4,4),(7,2)]
  | 13 => [(4,0),(7,0),(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0),(3,0)]
  | 17 => [(2,1),(2,5)]
  | 18 => [(0,2),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(4,4),(5,1),(5,4),(8,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2),(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(4,3),(5,3),(7,1),(8,3)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(4,0),(7,4),(8,0)]
  | 41 => [(1,3),(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => [(0,1),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(6,2)]
  | 53 => [(5,4),(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3),(6,3)]
  | 58 => [(7,2),(8,2)]
  | 59 => [(4,0),(5,0),(8,0)]
  | 60 => [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => [(0,3),(1,0),(3,0),(7,0)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(4,1),(8,1)]
  | 66 => [(0,2),(6,5)]
  | 67 => [(0,4),(1,1)]
  | 68 => [(5,1),(5,4)]
  | 69 => [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4)]
  | 71 => [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 72 => [(2,0),(7,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,5)]
  | 75 => [(7,0),(8,0)]
  | 76 => [(4,3),(8,3)]
  | 77 => [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(7,5),(8,2)]
  | 78 => [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => [(0,1),(1,4),(7,4)]
  | 81 => [(0,5),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(8,4)]
  | 83 => [(0,0),(1,4),(6,4),(7,4)]
  | 84 => [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => [(4,1),(4,5),(7,5),(8,5)]
  | 87 => [(0,2),(1,0),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(1,5),(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,1),(6,5)]
def root7Node81Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(7,2),(8,4)]
  | 1 => some [(4,0),(7,4)]
  | 2 => some [(1,3),(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5),(8,5)]
  | 6 => some [(1,1),(6,1),(7,1)]
  | 7 => some [(5,1),(8,1)]
  | 8 => some [(0,1),(6,5)]
  | 9 => some [(0,4),(6,2)]
  | 10 => some [(1,4),(7,4)]
  | 11 => some [(0,5),(6,3)]
  | 12 => some [(4,4),(7,2)]
  | 13 => some [(4,0),(7,0),(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0)]
  | 17 => some [(2,1),(2,5)]
  | 18 => some [(0,2),(6,0)]
  | 19 => some [(1,1),(7,1)]
  | 20 => some [(4,1),(7,5)]
  | 21 => some [(4,4),(5,1),(5,4),(8,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2),(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(4,3),(5,3),(7,1),(8,3)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(4,0),(7,4),(8,0)]
  | 41 => some [(1,3),(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => some [(0,1),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(6,2)]
  | 53 => some [(5,4),(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3),(6,3)]
  | 58 => some [(7,2),(8,2)]
  | 59 => some [(4,0),(5,0),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => some [(0,3),(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(4,1),(8,1)]
  | 66 => some [(0,2),(6,5)]
  | 67 => some [(0,4),(1,1)]
  | 68 => some [(5,1),(5,4)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(5,0),(5,3),(6,4)]
  | 71 => some [(0,5),(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,5)]
  | 72 => some [(2,0),(7,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,5)]
  | 75 => some [(7,0),(8,0)]
  | 76 => some [(4,3),(8,3)]
  | 77 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(7,5),(8,2)]
  | 78 => some [(0,0),(0,3),(0,4),(0,5),(6,0),(6,1),(6,2),(6,3)]
  | 79 => some [(3,1),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 80 => some [(0,1),(1,4),(7,4)]
  | 81 => some [(0,5),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(8,4)]
  | 83 => some [(0,0),(1,4),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(1,0),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(1,5),(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(6,0),(6,1),(6,5)]
theorem root7Node81Domains1_fast_eq : root7Node81Domains1 = expandDomains root7Node81Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node81Domains1 v = expandDomains root7Node81Domains1Fast v from by decide) v
theorem root7Node81Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Narrowing_checked :
    checkNarrowing table35 root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_flatten table35Scope [table35Rows0_0,table35Rows0_1,table35Rows0_2,table35Rows0_3,table35Rows0_4,table35Rows0_5,table35Rows1_0,table35Rows1_1,table35Rows1_2,table35Rows1_3,table35Rows1_4,table35Rows1_5,table35Rows2_0,table35Rows2_1,table35Rows2_2,table35Rows2_3,table35Rows2_4,table35Rows2_5,table35Rows3_0,table35Rows3_1,table35Rows3_2,table35Rows3_3,table35Rows3_4,table35Rows3_5,table35Rows4_0,table35Rows4_1,table35Rows4_2,table35Rows4_3,table35Rows4_4,table35Rows4_5,table35Rows5_0,table35Rows5_1,table35Rows5_2,table35Rows5_3,table35Rows5_4,table35Rows5_5,table35Rows6_0,table35Rows6_1,table35Rows6_2,table35Rows6_3,table35Rows6_4,table35Rows6_5,table35Rows7_0,table35Rows7_1,table35Rows7_2,table35Rows7_3,table35Rows7_4,table35Rows7_5,table35Rows8_0,table35Rows8_1,table35Rows8_2,table35Rows8_3,table35Rows8_4,table35Rows8_5]
    root7Node81Domains0 root7Node81Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node81Step1Chunk0_0_checked, root7Node81Step1Chunk0_1_checked, root7Node81Step1Chunk0_2_checked, root7Node81Step1Chunk0_3_checked, root7Node81Step1Chunk0_4_checked, root7Node81Step1Chunk0_5_checked, root7Node81Step1Chunk1_0_checked, root7Node81Step1Chunk1_1_checked, root7Node81Step1Chunk1_2_checked, root7Node81Step1Chunk1_3_checked, root7Node81Step1Chunk1_4_checked, root7Node81Step1Chunk1_5_checked, root7Node81Step1Chunk2_0_checked, root7Node81Step1Chunk2_1_checked, root7Node81Step1Chunk2_2_checked, root7Node81Step1Chunk2_3_checked, root7Node81Step1Chunk2_4_checked, root7Node81Step1Chunk2_5_checked, root7Node81Step1Chunk3_0_checked, root7Node81Step1Chunk3_1_checked, root7Node81Step1Chunk3_2_checked, root7Node81Step1Chunk3_3_checked, root7Node81Step1Chunk3_4_checked, root7Node81Step1Chunk3_5_checked, root7Node81Step1Chunk4_0_checked, root7Node81Step1Chunk4_1_checked, root7Node81Step1Chunk4_2_checked, root7Node81Step1Chunk4_3_checked, root7Node81Step1Chunk4_4_checked, root7Node81Step1Chunk4_5_checked, root7Node81Step1Chunk5_0_checked, root7Node81Step1Chunk5_1_checked, root7Node81Step1Chunk5_2_checked, root7Node81Step1Chunk5_3_checked, root7Node81Step1Chunk5_4_checked, root7Node81Step1Chunk5_5_checked, root7Node81Step1Chunk6_0_checked, root7Node81Step1Chunk6_1_checked, root7Node81Step1Chunk6_2_checked, root7Node81Step1Chunk6_3_checked, root7Node81Step1Chunk6_4_checked, root7Node81Step1Chunk6_5_checked, root7Node81Step1Chunk7_0_checked, root7Node81Step1Chunk7_1_checked, root7Node81Step1Chunk7_2_checked, root7Node81Step1Chunk7_3_checked, root7Node81Step1Chunk7_4_checked, root7Node81Step1Chunk7_5_checked, root7Node81Step1Chunk8_0_checked, root7Node81Step1Chunk8_1_checked, root7Node81Step1Chunk8_2_checked, root7Node81Step1Chunk8_3_checked, root7Node81Step1Chunk8_4_checked, root7Node81Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node81Step1_checked :
    checkReplacement table35 root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq
    root7Node81Step1Narrowing_checked (by decide)
def root7Node81Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(7,2),(8,4)]
  | 1 => [(4,0),(7,4)]
  | 2 => [(1,3),(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(5,5),(8,5)]
  | 6 => [(1,1),(6,1),(7,1)]
  | 7 => [(5,1),(8,1)]
  | 8 => [(0,1),(6,5)]
  | 9 => [(0,4),(6,2)]
  | 10 => [(1,4),(7,4)]
  | 11 => [(0,5),(6,3)]
  | 12 => [(4,4),(7,2)]
  | 13 => [(4,0),(7,0),(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0),(3,0)]
  | 17 => [(2,1),(2,5)]
  | 18 => [(0,2),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(4,4),(5,1),(5,4),(8,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2),(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(4,3),(5,3),(7,1),(8,3)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(4,0),(7,4),(8,0)]
  | 41 => [(1,3),(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => [(0,1),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(6,2)]
  | 53 => [(5,4),(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3),(6,3)]
  | 58 => [(7,2),(8,2)]
  | 59 => [(4,0),(5,0),(8,0)]
  | 60 => [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => [(0,3),(1,0),(7,0)]
  | 62 => [(4,3),(7,1),(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(4,1),(8,1)]
  | 66 => [(0,2),(6,5)]
  | 67 => [(0,4),(1,1)]
  | 68 => [(5,1),(5,4)]
  | 69 => [(0,0),(0,1),(6,4)]
  | 70 => [(1,4),(5,0),(5,3)]
  | 71 => [(0,5),(4,5),(5,5),(8,5)]
  | 72 => [(2,0),(7,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,5)]
  | 75 => [(7,0),(8,0)]
  | 76 => [(4,3),(8,3)]
  | 77 => [(1,5),(3,5),(5,5),(7,5)]
  | 78 => [(0,0),(0,5),(6,0),(6,3)]
  | 79 => [(3,1),(4,4),(7,2)]
  | 80 => [(0,1),(1,4),(7,4)]
  | 81 => [(0,5),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(8,4)]
  | 83 => [(1,4),(7,4)]
  | 84 => [(0,5),(1,3),(6,3)]
  | 85 => [(1,1),(5,0),(6,1),(7,1)]
  | 86 => [(4,1),(4,5),(7,5)]
  | 87 => [(0,2),(1,0),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(6,0),(6,5)]
def root7Node81Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(7,2),(8,4)]
  | 1 => some [(4,0),(7,4)]
  | 2 => some [(1,3),(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5),(8,5)]
  | 6 => some [(1,1),(6,1),(7,1)]
  | 7 => some [(5,1),(8,1)]
  | 8 => some [(0,1),(6,5)]
  | 9 => some [(0,4),(6,2)]
  | 10 => some [(1,4),(7,4)]
  | 11 => some [(0,5),(6,3)]
  | 12 => some [(4,4),(7,2)]
  | 13 => some [(4,0),(7,0),(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0)]
  | 17 => some [(2,1),(2,5)]
  | 18 => some [(0,2),(6,0)]
  | 19 => some [(1,1),(7,1)]
  | 20 => some [(4,1),(7,5)]
  | 21 => some [(4,4),(5,1),(5,4),(8,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2),(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(4,3),(5,3),(7,1),(8,3)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(4,0),(7,4),(8,0)]
  | 41 => some [(1,3),(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => some [(0,1),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(6,2)]
  | 53 => some [(5,4),(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3),(6,3)]
  | 58 => some [(7,2),(8,2)]
  | 59 => some [(4,0),(5,0),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => some [(0,3),(1,0),(7,0)]
  | 62 => some [(4,3),(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(4,1),(8,1)]
  | 66 => some [(0,2),(6,5)]
  | 67 => some [(0,4),(1,1)]
  | 68 => some [(5,1),(5,4)]
  | 69 => some [(0,0),(0,1),(6,4)]
  | 70 => some [(1,4),(5,0),(5,3)]
  | 71 => some [(0,5),(4,5),(5,5),(8,5)]
  | 72 => some [(2,0),(7,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,5)]
  | 75 => some [(7,0),(8,0)]
  | 76 => some [(4,3),(8,3)]
  | 77 => some [(1,5),(3,5),(5,5),(7,5)]
  | 78 => some [(0,0),(0,5),(6,0),(6,3)]
  | 79 => some [(3,1),(4,4),(7,2)]
  | 80 => some [(0,1),(1,4),(7,4)]
  | 81 => some [(0,5),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(8,4)]
  | 83 => some [(1,4),(7,4)]
  | 84 => some [(0,5),(1,3),(6,3)]
  | 85 => some [(1,1),(5,0),(6,1),(7,1)]
  | 86 => some [(4,1),(4,5),(7,5)]
  | 87 => some [(0,2),(1,0),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(6,0),(6,5)]
theorem root7Node81Domains2_fast_eq : root7Node81Domains2 = expandDomains root7Node81Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node81Domains2 v = expandDomains root7Node81Domains2Fast v from by decide) v
theorem root7Node81Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq (by decide)
theorem root7Node81Step2Narrowing_checked :
    checkNarrowing table65 root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root7Node81Domains1 root7Node81Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node81Step2Chunk0_0_checked, root7Node81Step2Chunk0_1_checked, root7Node81Step2Chunk0_2_checked, root7Node81Step2Chunk0_3_checked, root7Node81Step2Chunk0_4_checked, root7Node81Step2Chunk0_5_checked, root7Node81Step2Chunk1_0_checked, root7Node81Step2Chunk1_1_checked, root7Node81Step2Chunk1_2_checked, root7Node81Step2Chunk1_3_checked, root7Node81Step2Chunk1_4_checked, root7Node81Step2Chunk1_5_checked, root7Node81Step2Chunk2_0_checked, root7Node81Step2Chunk2_1_checked, root7Node81Step2Chunk2_2_checked, root7Node81Step2Chunk2_3_checked, root7Node81Step2Chunk2_4_checked, root7Node81Step2Chunk2_5_checked, root7Node81Step2Chunk3_0_checked, root7Node81Step2Chunk3_1_checked, root7Node81Step2Chunk3_2_checked, root7Node81Step2Chunk3_3_checked, root7Node81Step2Chunk3_4_checked, root7Node81Step2Chunk3_5_checked, root7Node81Step2Chunk4_0_checked, root7Node81Step2Chunk4_1_checked, root7Node81Step2Chunk4_2_checked, root7Node81Step2Chunk4_3_checked, root7Node81Step2Chunk4_4_checked, root7Node81Step2Chunk4_5_checked, root7Node81Step2Chunk5_0_checked, root7Node81Step2Chunk5_1_checked, root7Node81Step2Chunk5_2_checked, root7Node81Step2Chunk5_3_checked, root7Node81Step2Chunk5_4_checked, root7Node81Step2Chunk5_5_checked, root7Node81Step2Chunk6_0_checked, root7Node81Step2Chunk6_1_checked, root7Node81Step2Chunk6_2_checked, root7Node81Step2Chunk6_3_checked, root7Node81Step2Chunk6_4_checked, root7Node81Step2Chunk6_5_checked, root7Node81Step2Chunk7_0_checked, root7Node81Step2Chunk7_1_checked, root7Node81Step2Chunk7_2_checked, root7Node81Step2Chunk7_3_checked, root7Node81Step2Chunk7_4_checked, root7Node81Step2Chunk7_5_checked, root7Node81Step2Chunk8_0_checked, root7Node81Step2Chunk8_1_checked, root7Node81Step2Chunk8_2_checked, root7Node81Step2Chunk8_3_checked, root7Node81Step2Chunk8_4_checked, root7Node81Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node81Step2_checked :
    checkReplacement table65 root7Node81Domains1 root7Node81Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node81Domains1 root7Node81Domains2
    root7Node81Domains1Fast root7Node81Domains2Fast
    root7Node81Domains1_fast_eq root7Node81Domains2_fast_eq
    root7Node81Step2Narrowing_checked (by decide)
def root7Node81Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(7,2),(8,4)]
  | 1 => [(4,0),(7,4)]
  | 2 => [(1,3),(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(5,5),(8,5)]
  | 6 => [(1,1),(6,1),(7,1)]
  | 7 => [(5,1),(8,1)]
  | 8 => [(0,1),(6,5)]
  | 9 => [(0,4),(6,2)]
  | 10 => [(1,4),(7,4)]
  | 11 => [(0,5),(6,3)]
  | 12 => [(4,4),(7,2)]
  | 13 => [(4,0),(7,0),(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0),(3,0)]
  | 17 => [(2,1),(2,5)]
  | 18 => [(0,2),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(4,4),(5,1),(5,4),(8,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2),(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(4,3),(5,3),(7,1),(8,3)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(4,0),(7,4),(8,0)]
  | 41 => [(1,3),(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5),(7,5)]
  | 51 => [(0,1),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(6,2)]
  | 53 => [(5,4),(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3),(6,3)]
  | 58 => [(7,2),(8,2)]
  | 59 => [(4,0),(5,0),(8,0)]
  | 60 => [(4,5),(7,3)]
  | 61 => [(0,3),(1,0),(7,0)]
  | 62 => [(4,3),(7,1),(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(4,1),(8,1)]
  | 66 => [(0,2),(6,5)]
  | 67 => [(0,4),(1,1)]
  | 68 => [(5,1),(5,4)]
  | 69 => [(0,0),(0,1),(6,4)]
  | 70 => [(1,4),(5,0),(5,3)]
  | 71 => [(0,5),(4,5),(5,5),(8,5)]
  | 72 => [(2,0),(7,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,5)]
  | 75 => [(7,0),(8,0)]
  | 76 => [(4,3),(8,3)]
  | 77 => [(1,5),(3,5),(5,5),(7,5)]
  | 78 => [(0,0),(0,5),(6,0),(6,3)]
  | 79 => [(3,1),(4,4),(7,2)]
  | 80 => [(0,1),(1,4),(7,4)]
  | 81 => [(0,5),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(8,4)]
  | 83 => [(1,4),(7,4)]
  | 84 => [(0,5),(1,3),(6,3)]
  | 85 => [(1,1),(5,0),(6,1),(7,1)]
  | 86 => [(4,1),(4,5),(7,5)]
  | 87 => [(0,2),(1,0),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(6,0),(6,5)]
def root7Node81Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(7,2),(8,4)]
  | 1 => some [(4,0),(7,4)]
  | 2 => some [(1,3),(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5),(8,5)]
  | 6 => some [(1,1),(6,1),(7,1)]
  | 7 => some [(5,1),(8,1)]
  | 8 => some [(0,1),(6,5)]
  | 9 => some [(0,4),(6,2)]
  | 10 => some [(1,4),(7,4)]
  | 11 => some [(0,5),(6,3)]
  | 12 => some [(4,4),(7,2)]
  | 13 => some [(4,0),(7,0),(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0)]
  | 17 => some [(2,1),(2,5)]
  | 18 => some [(0,2),(6,0)]
  | 19 => some [(1,1),(7,1)]
  | 20 => some [(4,1),(7,5)]
  | 21 => some [(4,4),(5,1),(5,4),(8,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2),(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(4,3),(5,3),(7,1),(8,3)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(4,0),(7,4),(8,0)]
  | 41 => some [(1,3),(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(0,1),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(6,2)]
  | 53 => some [(5,4),(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3),(6,3)]
  | 58 => some [(7,2),(8,2)]
  | 59 => some [(4,0),(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3),(1,0),(7,0)]
  | 62 => some [(4,3),(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(4,1),(8,1)]
  | 66 => some [(0,2),(6,5)]
  | 67 => some [(0,4),(1,1)]
  | 68 => some [(5,1),(5,4)]
  | 69 => some [(0,0),(0,1),(6,4)]
  | 70 => some [(1,4),(5,0),(5,3)]
  | 71 => some [(0,5),(4,5),(5,5),(8,5)]
  | 72 => some [(2,0),(7,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,5)]
  | 75 => some [(7,0),(8,0)]
  | 76 => some [(4,3),(8,3)]
  | 77 => some [(1,5),(3,5),(5,5),(7,5)]
  | 78 => some [(0,0),(0,5),(6,0),(6,3)]
  | 79 => some [(3,1),(4,4),(7,2)]
  | 80 => some [(0,1),(1,4),(7,4)]
  | 81 => some [(0,5),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(8,4)]
  | 83 => some [(1,4),(7,4)]
  | 84 => some [(0,5),(1,3),(6,3)]
  | 85 => some [(1,1),(5,0),(6,1),(7,1)]
  | 86 => some [(4,1),(4,5),(7,5)]
  | 87 => some [(0,2),(1,0),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(6,0),(6,5)]
theorem root7Node81Domains3_fast_eq : root7Node81Domains3 = expandDomains root7Node81Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node81Domains3 v = expandDomains root7Node81Domains3Fast v from by decide) v
theorem root7Node81Step3Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq (by decide)
theorem root7Node81Step3Narrowing_checked :
    checkNarrowing table19 root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkNarrowing_flatten table19Scope [table19Rows0_0,table19Rows0_1,table19Rows0_2,table19Rows0_3,table19Rows0_4,table19Rows0_5,table19Rows1_0,table19Rows1_1,table19Rows1_2,table19Rows1_3,table19Rows1_4,table19Rows1_5,table19Rows2_0,table19Rows2_1,table19Rows2_2,table19Rows2_3,table19Rows2_4,table19Rows2_5,table19Rows3_0,table19Rows3_1,table19Rows3_2,table19Rows3_3,table19Rows3_4,table19Rows3_5,table19Rows4_0,table19Rows4_1,table19Rows4_2,table19Rows4_3,table19Rows4_4,table19Rows4_5,table19Rows5_0,table19Rows5_1,table19Rows5_2,table19Rows5_3,table19Rows5_4,table19Rows5_5,table19Rows6_0,table19Rows6_1,table19Rows6_2,table19Rows6_3,table19Rows6_4,table19Rows6_5,table19Rows7_0,table19Rows7_1,table19Rows7_2,table19Rows7_3,table19Rows7_4,table19Rows7_5,table19Rows8_0,table19Rows8_1,table19Rows8_2,table19Rows8_3,table19Rows8_4,table19Rows8_5]
    root7Node81Domains2 root7Node81Domains3 (by
      simp only [List.all_cons, List.all_nil, root7Node81Step3Chunk0_0_checked, root7Node81Step3Chunk0_1_checked, root7Node81Step3Chunk0_2_checked, root7Node81Step3Chunk0_3_checked, root7Node81Step3Chunk0_4_checked, root7Node81Step3Chunk0_5_checked, root7Node81Step3Chunk1_0_checked, root7Node81Step3Chunk1_1_checked, root7Node81Step3Chunk1_2_checked, root7Node81Step3Chunk1_3_checked, root7Node81Step3Chunk1_4_checked, root7Node81Step3Chunk1_5_checked, root7Node81Step3Chunk2_0_checked, root7Node81Step3Chunk2_1_checked, root7Node81Step3Chunk2_2_checked, root7Node81Step3Chunk2_3_checked, root7Node81Step3Chunk2_4_checked, root7Node81Step3Chunk2_5_checked, root7Node81Step3Chunk3_0_checked, root7Node81Step3Chunk3_1_checked, root7Node81Step3Chunk3_2_checked, root7Node81Step3Chunk3_3_checked, root7Node81Step3Chunk3_4_checked, root7Node81Step3Chunk3_5_checked, root7Node81Step3Chunk4_0_checked, root7Node81Step3Chunk4_1_checked, root7Node81Step3Chunk4_2_checked, root7Node81Step3Chunk4_3_checked, root7Node81Step3Chunk4_4_checked, root7Node81Step3Chunk4_5_checked, root7Node81Step3Chunk5_0_checked, root7Node81Step3Chunk5_1_checked, root7Node81Step3Chunk5_2_checked, root7Node81Step3Chunk5_3_checked, root7Node81Step3Chunk5_4_checked, root7Node81Step3Chunk5_5_checked, root7Node81Step3Chunk6_0_checked, root7Node81Step3Chunk6_1_checked, root7Node81Step3Chunk6_2_checked, root7Node81Step3Chunk6_3_checked, root7Node81Step3Chunk6_4_checked, root7Node81Step3Chunk6_5_checked, root7Node81Step3Chunk7_0_checked, root7Node81Step3Chunk7_1_checked, root7Node81Step3Chunk7_2_checked, root7Node81Step3Chunk7_3_checked, root7Node81Step3Chunk7_4_checked, root7Node81Step3Chunk7_5_checked, root7Node81Step3Chunk8_0_checked, root7Node81Step3Chunk8_1_checked, root7Node81Step3Chunk8_2_checked, root7Node81Step3Chunk8_3_checked, root7Node81Step3Chunk8_4_checked, root7Node81Step3Chunk8_5_checked, Bool.true_and])
theorem root7Node81Step3_checked :
    checkReplacement table19 root7Node81Domains2 root7Node81Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root7Node81Domains2 root7Node81Domains3
    root7Node81Domains2Fast root7Node81Domains3Fast
    root7Node81Domains2_fast_eq root7Node81Domains3_fast_eq
    root7Node81Step3Narrowing_checked (by decide)
def root7Node81Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,2)]
  | 1 => [(4,0),(7,4)]
  | 2 => [(1,3),(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(5,5),(8,5)]
  | 6 => [(1,1),(6,1)]
  | 7 => [(5,1),(8,1)]
  | 8 => [(0,1),(6,5)]
  | 9 => [(0,4),(6,2)]
  | 10 => [(1,4),(7,4)]
  | 11 => [(0,5),(6,3)]
  | 12 => [(4,4),(7,2)]
  | 13 => [(7,0),(8,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0),(3,0)]
  | 17 => [(2,1),(2,5)]
  | 18 => [(0,2),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(4,4),(5,4),(8,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(4,4)]
  | 25 => [(0,0)]
  | 26 => [(3,2),(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(4,3),(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1)]
  | 37 => [(0,1)]
  | 38 => [(6,2)]
  | 39 => [(8,4)]
  | 40 => [(4,0),(7,4),(8,0)]
  | 41 => [(1,3),(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(8,5)]
  | 48 => [(1,0)]
  | 49 => [(7,1)]
  | 50 => [(1,5),(7,5)]
  | 51 => [(0,1),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(6,2)]
  | 53 => [(5,4),(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3),(6,3)]
  | 58 => [(7,2),(8,2)]
  | 59 => [(4,0),(5,0),(8,0)]
  | 60 => [(4,5),(7,3)]
  | 61 => [(0,3),(1,0),(7,0)]
  | 62 => [(4,3),(7,1),(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(4,1),(8,1)]
  | 66 => [(0,2),(6,5)]
  | 67 => [(0,4),(1,1)]
  | 68 => [(5,1),(5,4)]
  | 69 => [(0,0),(0,1),(6,4)]
  | 70 => [(1,4),(5,0),(5,3)]
  | 71 => [(0,5),(4,5),(5,5),(8,5)]
  | 72 => [(2,0),(7,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,5)]
  | 75 => [(7,0),(8,0)]
  | 76 => [(4,3),(8,3)]
  | 77 => [(1,5),(3,5),(5,5),(7,5)]
  | 78 => [(0,0),(0,5),(6,0),(6,3)]
  | 79 => [(3,1),(4,4),(7,2)]
  | 80 => [(0,1),(1,4),(7,4)]
  | 81 => [(0,5),(6,2),(6,3)]
  | 82 => [(4,4),(7,2),(8,4)]
  | 83 => [(1,4),(7,4)]
  | 84 => [(0,5),(1,3),(6,3)]
  | 85 => [(1,1),(5,0),(6,1),(7,1)]
  | 86 => [(4,1),(4,5),(7,5)]
  | 87 => [(0,2),(1,0),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(4,1),(7,5),(8,1)]
  | _ => [(0,2),(6,0),(6,5)]
def root7Node81Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,2)]
  | 1 => some [(4,0),(7,4)]
  | 2 => some [(1,3),(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(5,5),(8,5)]
  | 6 => some [(1,1),(6,1)]
  | 7 => some [(5,1),(8,1)]
  | 8 => some [(0,1),(6,5)]
  | 9 => some [(0,4),(6,2)]
  | 10 => some [(1,4),(7,4)]
  | 11 => some [(0,5),(6,3)]
  | 12 => some [(4,4),(7,2)]
  | 13 => some [(7,0),(8,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0)]
  | 17 => some [(2,1),(2,5)]
  | 18 => some [(0,2),(6,0)]
  | 19 => some [(1,1),(7,1)]
  | 20 => some [(4,1),(7,5)]
  | 21 => some [(4,4),(5,4),(8,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(4,4)]
  | 25 => some [(0,0)]
  | 26 => some [(3,2),(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(4,3),(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(1,5)]
  | 35 => some [(6,1)]
  | 36 => some [(5,1)]
  | 37 => some [(0,1)]
  | 38 => some [(6,2)]
  | 39 => some [(8,4)]
  | 40 => some [(4,0),(7,4),(8,0)]
  | 41 => some [(1,3),(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(8,3)]
  | 47 => some [(8,5)]
  | 48 => some [(1,0)]
  | 49 => some [(7,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(0,1),(6,4),(6,5)]
  | 52 => some [(0,4),(1,2),(6,2)]
  | 53 => some [(5,4),(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3),(6,3)]
  | 58 => some [(7,2),(8,2)]
  | 59 => some [(4,0),(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(0,3),(1,0),(7,0)]
  | 62 => some [(4,3),(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(4,1),(8,1)]
  | 66 => some [(0,2),(6,5)]
  | 67 => some [(0,4),(1,1)]
  | 68 => some [(5,1),(5,4)]
  | 69 => some [(0,0),(0,1),(6,4)]
  | 70 => some [(1,4),(5,0),(5,3)]
  | 71 => some [(0,5),(4,5),(5,5),(8,5)]
  | 72 => some [(2,0),(7,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,5)]
  | 75 => some [(7,0),(8,0)]
  | 76 => some [(4,3),(8,3)]
  | 77 => some [(1,5),(3,5),(5,5),(7,5)]
  | 78 => some [(0,0),(0,5),(6,0),(6,3)]
  | 79 => some [(3,1),(4,4),(7,2)]
  | 80 => some [(0,1),(1,4),(7,4)]
  | 81 => some [(0,5),(6,2),(6,3)]
  | 82 => some [(4,4),(7,2),(8,4)]
  | 83 => some [(1,4),(7,4)]
  | 84 => some [(0,5),(1,3),(6,3)]
  | 85 => some [(1,1),(5,0),(6,1),(7,1)]
  | 86 => some [(4,1),(4,5),(7,5)]
  | 87 => some [(0,2),(1,0),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(6,0),(6,5)]
theorem root7Node81Domains4_fast_eq : root7Node81Domains4 = expandDomains root7Node81Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node81Domains4 v = expandDomains root7Node81Domains4Fast v from by decide) v
theorem root7Node81Step4Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq (by decide)
theorem root7Node81Step4Narrowing_checked :
    checkNarrowing table0 root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkNarrowing_flatten table0Scope [table0Rows0_0,table0Rows0_1,table0Rows0_2,table0Rows0_3,table0Rows0_4,table0Rows0_5,table0Rows1_0,table0Rows1_1,table0Rows1_2,table0Rows1_3,table0Rows1_4,table0Rows1_5,table0Rows2_0,table0Rows2_1,table0Rows2_2,table0Rows2_3,table0Rows2_4,table0Rows2_5,table0Rows3_0,table0Rows3_1,table0Rows3_2,table0Rows3_3,table0Rows3_4,table0Rows3_5,table0Rows4_0,table0Rows4_1,table0Rows4_2,table0Rows4_3,table0Rows4_4,table0Rows4_5,table0Rows5_0,table0Rows5_1,table0Rows5_2,table0Rows5_3,table0Rows5_4,table0Rows5_5,table0Rows6_0,table0Rows6_1,table0Rows6_2,table0Rows6_3,table0Rows6_4,table0Rows6_5,table0Rows7_0,table0Rows7_1,table0Rows7_2,table0Rows7_3,table0Rows7_4,table0Rows7_5,table0Rows8_0,table0Rows8_1,table0Rows8_2,table0Rows8_3,table0Rows8_4,table0Rows8_5]
    root7Node81Domains3 root7Node81Domains4 (by
      simp only [List.all_cons, List.all_nil, root7Node81Step4Chunk0_0_checked, root7Node81Step4Chunk0_1_checked, root7Node81Step4Chunk0_2_checked, root7Node81Step4Chunk0_3_checked, root7Node81Step4Chunk0_4_checked, root7Node81Step4Chunk0_5_checked, root7Node81Step4Chunk1_0_checked, root7Node81Step4Chunk1_1_checked, root7Node81Step4Chunk1_2_checked, root7Node81Step4Chunk1_3_checked, root7Node81Step4Chunk1_4_checked, root7Node81Step4Chunk1_5_checked, root7Node81Step4Chunk2_0_checked, root7Node81Step4Chunk2_1_checked, root7Node81Step4Chunk2_2_checked, root7Node81Step4Chunk2_3_checked, root7Node81Step4Chunk2_4_checked, root7Node81Step4Chunk2_5_checked, root7Node81Step4Chunk3_0_checked, root7Node81Step4Chunk3_1_checked, root7Node81Step4Chunk3_2_checked, root7Node81Step4Chunk3_3_checked, root7Node81Step4Chunk3_4_checked, root7Node81Step4Chunk3_5_checked, root7Node81Step4Chunk4_0_checked, root7Node81Step4Chunk4_1_checked, root7Node81Step4Chunk4_2_checked, root7Node81Step4Chunk4_3_checked, root7Node81Step4Chunk4_4_checked, root7Node81Step4Chunk4_5_checked, root7Node81Step4Chunk5_0_checked, root7Node81Step4Chunk5_1_checked, root7Node81Step4Chunk5_2_checked, root7Node81Step4Chunk5_3_checked, root7Node81Step4Chunk5_4_checked, root7Node81Step4Chunk5_5_checked, root7Node81Step4Chunk6_0_checked, root7Node81Step4Chunk6_1_checked, root7Node81Step4Chunk6_2_checked, root7Node81Step4Chunk6_3_checked, root7Node81Step4Chunk6_4_checked, root7Node81Step4Chunk6_5_checked, root7Node81Step4Chunk7_0_checked, root7Node81Step4Chunk7_1_checked, root7Node81Step4Chunk7_2_checked, root7Node81Step4Chunk7_3_checked, root7Node81Step4Chunk7_4_checked, root7Node81Step4Chunk7_5_checked, root7Node81Step4Chunk8_0_checked, root7Node81Step4Chunk8_1_checked, root7Node81Step4Chunk8_2_checked, root7Node81Step4Chunk8_3_checked, root7Node81Step4Chunk8_4_checked, root7Node81Step4Chunk8_5_checked, Bool.true_and])
theorem root7Node81Step4_checked :
    checkReplacement table0 root7Node81Domains3 root7Node81Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root7Node81Domains3 root7Node81Domains4
    root7Node81Domains3Fast root7Node81Domains4Fast
    root7Node81Domains3_fast_eq root7Node81Domains4_fast_eq
    root7Node81Step4Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
