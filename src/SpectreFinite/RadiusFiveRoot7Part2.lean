module

public import SpectreFinite.RadiusFiveRoot7Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable0
public import SpectreFinite.RadiusFiveTable4
public import SpectreFinite.RadiusFiveTable44
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node2Domains0 : Domains 91 State := restrict root7Node1Domains4 14 (7,3)
def root7Node2Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 14 => some [(7,3)]
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
theorem root7Node2Domains0_fast_eq : root7Node2Domains0 = expandDomains root7Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node2Domains0 v = expandDomains root7Node2Domains0Fast v from by decide) v
def root7Node2Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(7,2),(8,4)]
  | 1 => [(1,4),(4,0),(7,4)]
  | 2 => [(0,5),(1,3),(6,3),(7,3)]
  | 3 => [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 4 => [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 5 => [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => [(1,1),(7,1)]
  | 7 => [(4,1),(7,5)]
  | 8 => [(0,2),(6,0)]
  | 9 => [(1,1),(3,1),(7,1)]
  | 10 => [(0,1),(1,5),(6,5)]
  | 11 => [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => [(4,0),(8,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2),(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0),(7,0)]
  | 19 => [(1,1),(4,3),(7,1),(8,3)]
  | 20 => [(4,1),(7,5),(8,5)]
  | 21 => [(5,1),(5,4),(8,4)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(4,2),(5,2),(8,2)]
  | 30 => [(4,3),(5,3),(7,1),(8,3)]
  | 31 => [(7,5),(8,5)]
  | 32 => [(0,3),(1,0)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1),(8,1)]
  | 37 => [(0,1),(6,5)]
  | 38 => [(0,4),(6,2)]
  | 39 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => [(4,0),(7,4),(8,0)]
  | 41 => [(1,3),(7,3)]
  | 42 => [(4,2),(8,2)]
  | 43 => [(5,0),(5,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5),(8,5)]
  | 48 => [(1,0),(3,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => [(0,1),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(6,2)]
  | 53 => [(1,4),(3,4),(5,4),(7,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(4,4),(7,2),(8,2)]
  | 59 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => [(0,3),(1,0),(3,0),(7,0)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(7,1)]
  | 68 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => [(0,0),(1,3),(1,4),(3,3),(6,4)]
  | 71 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 72 => [(2,0),(4,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2)]
  | 75 => [(5,0),(7,0),(8,0)]
  | 76 => [(4,3),(4,5),(7,3),(8,3)]
  | 77 => [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(7,5),(8,2)]
  | 78 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 79 => [(3,1),(5,1),(5,4),(8,4)]
  | 80 => [(0,1),(1,4)]
  | 81 => [(0,5),(6,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(1,4),(6,4),(7,4)]
  | 84 => [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => [(4,1),(4,5),(7,5),(8,5)]
  | 87 => [(0,2),(1,0),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(1,5),(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,1),(6,5)]
def root7Node2Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(7,2),(8,4)]
  | 1 => some [(1,4),(4,0),(7,4)]
  | 2 => some [(0,5),(1,3),(6,3),(7,3)]
  | 3 => some [(2,0),(2,2),(2,4),(4,2),(4,4)]
  | 4 => some [(0,0),(1,3),(3,3),(5,3),(7,3)]
  | 5 => some [(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 6 => some [(1,1),(7,1)]
  | 7 => some [(4,1),(7,5)]
  | 8 => some [(0,2),(6,0)]
  | 9 => some [(1,1),(3,1),(7,1)]
  | 10 => some [(0,1),(1,5),(6,5)]
  | 11 => some [(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 12 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(4,0),(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2),(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(1,1),(4,3),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(5,1),(5,4),(8,4)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(4,2),(5,2),(8,2)]
  | 30 => some [(4,3),(5,3),(7,1),(8,3)]
  | 31 => some [(7,5),(8,5)]
  | 32 => some [(0,3),(1,0)]
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
  | 53 => some [(1,4),(3,4),(5,4),(7,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => some [(0,3),(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(6,4)]
  | 71 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 72 => some [(2,0),(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(5,0),(7,0),(8,0)]
  | 76 => some [(4,3),(4,5),(7,3),(8,3)]
  | 77 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(7,5),(8,2)]
  | 78 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 79 => some [(3,1),(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4)]
  | 81 => some [(0,5),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(1,4),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(1,0),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(1,5),(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(6,0),(6,1),(6,5)]
theorem root7Node2Domains1_fast_eq : root7Node2Domains1 = expandDomains root7Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node2Domains1 v = expandDomains root7Node2Domains1Fast v from by decide) v
theorem root7Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_0⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_1⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_2⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_3⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_4⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_5⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_0⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_1⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_2⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_3⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_4⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_5⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_0⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_1⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_2⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_3⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_4⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_5⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_0⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_1⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_2⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_3⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_4⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_5⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_0⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_1⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_2⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_3⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_4⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_5⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_0⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_1⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_2⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_3⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_4⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk5_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_5⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk6_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_0⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk6_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_1⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk6_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_2⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk6_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_3⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk6_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_4⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk6_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_5⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk7_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_0⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk7_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_1⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk7_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_2⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk7_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_3⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk7_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_4⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk7_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_5⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk8_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_0⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk8_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_1⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk8_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_2⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk8_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_3⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk8_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_4⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Chunk8_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_5⟩
      root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq (by decide)
theorem root7Node2Step1Narrowing_checked :
    checkNarrowing table44 root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkNarrowing_flatten table44Scope [table44Rows0_0,table44Rows0_1,table44Rows0_2,table44Rows0_3,table44Rows0_4,table44Rows0_5,table44Rows1_0,table44Rows1_1,table44Rows1_2,table44Rows1_3,table44Rows1_4,table44Rows1_5,table44Rows2_0,table44Rows2_1,table44Rows2_2,table44Rows2_3,table44Rows2_4,table44Rows2_5,table44Rows3_0,table44Rows3_1,table44Rows3_2,table44Rows3_3,table44Rows3_4,table44Rows3_5,table44Rows4_0,table44Rows4_1,table44Rows4_2,table44Rows4_3,table44Rows4_4,table44Rows4_5,table44Rows5_0,table44Rows5_1,table44Rows5_2,table44Rows5_3,table44Rows5_4,table44Rows5_5,table44Rows6_0,table44Rows6_1,table44Rows6_2,table44Rows6_3,table44Rows6_4,table44Rows6_5,table44Rows7_0,table44Rows7_1,table44Rows7_2,table44Rows7_3,table44Rows7_4,table44Rows7_5,table44Rows8_0,table44Rows8_1,table44Rows8_2,table44Rows8_3,table44Rows8_4,table44Rows8_5]
    root7Node2Domains0 root7Node2Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node2Step1Chunk0_0_checked, root7Node2Step1Chunk0_1_checked, root7Node2Step1Chunk0_2_checked, root7Node2Step1Chunk0_3_checked, root7Node2Step1Chunk0_4_checked, root7Node2Step1Chunk0_5_checked, root7Node2Step1Chunk1_0_checked, root7Node2Step1Chunk1_1_checked, root7Node2Step1Chunk1_2_checked, root7Node2Step1Chunk1_3_checked, root7Node2Step1Chunk1_4_checked, root7Node2Step1Chunk1_5_checked, root7Node2Step1Chunk2_0_checked, root7Node2Step1Chunk2_1_checked, root7Node2Step1Chunk2_2_checked, root7Node2Step1Chunk2_3_checked, root7Node2Step1Chunk2_4_checked, root7Node2Step1Chunk2_5_checked, root7Node2Step1Chunk3_0_checked, root7Node2Step1Chunk3_1_checked, root7Node2Step1Chunk3_2_checked, root7Node2Step1Chunk3_3_checked, root7Node2Step1Chunk3_4_checked, root7Node2Step1Chunk3_5_checked, root7Node2Step1Chunk4_0_checked, root7Node2Step1Chunk4_1_checked, root7Node2Step1Chunk4_2_checked, root7Node2Step1Chunk4_3_checked, root7Node2Step1Chunk4_4_checked, root7Node2Step1Chunk4_5_checked, root7Node2Step1Chunk5_0_checked, root7Node2Step1Chunk5_1_checked, root7Node2Step1Chunk5_2_checked, root7Node2Step1Chunk5_3_checked, root7Node2Step1Chunk5_4_checked, root7Node2Step1Chunk5_5_checked, root7Node2Step1Chunk6_0_checked, root7Node2Step1Chunk6_1_checked, root7Node2Step1Chunk6_2_checked, root7Node2Step1Chunk6_3_checked, root7Node2Step1Chunk6_4_checked, root7Node2Step1Chunk6_5_checked, root7Node2Step1Chunk7_0_checked, root7Node2Step1Chunk7_1_checked, root7Node2Step1Chunk7_2_checked, root7Node2Step1Chunk7_3_checked, root7Node2Step1Chunk7_4_checked, root7Node2Step1Chunk7_5_checked, root7Node2Step1Chunk8_0_checked, root7Node2Step1Chunk8_1_checked, root7Node2Step1Chunk8_2_checked, root7Node2Step1Chunk8_3_checked, root7Node2Step1Chunk8_4_checked, root7Node2Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node2Step1_checked :
    checkReplacement table44 root7Node2Domains0 root7Node2Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node2Domains0 root7Node2Domains1
    root7Node2Domains0Fast root7Node2Domains1Fast
    root7Node2Domains0_fast_eq root7Node2Domains1_fast_eq
    root7Node2Step1Narrowing_checked (by decide)
def root7Node2Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(7,2),(8,4)]
  | 1 => [(1,4),(7,4)]
  | 2 => [(0,5),(6,3)]
  | 3 => [(2,0),(2,2),(2,4),(4,4)]
  | 4 => [(0,0),(1,3),(3,3),(7,3)]
  | 5 => [(3,2),(5,2),(7,2)]
  | 6 => [(1,1),(7,1)]
  | 7 => [(4,1),(7,5)]
  | 8 => [(0,2),(6,0)]
  | 9 => [(1,1),(3,1),(7,1)]
  | 10 => [(0,1),(1,5),(6,5)]
  | 11 => [(0,4),(6,1),(6,2)]
  | 12 => [(5,1),(5,4),(8,4)]
  | 13 => [(4,0),(8,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2),(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0),(7,0)]
  | 19 => [(4,3),(7,1),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(5,1),(5,4),(8,4)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(4,2),(8,2)]
  | 30 => [(4,3),(5,3),(7,1),(8,3)]
  | 31 => [(7,5),(8,5)]
  | 32 => [(0,3),(1,0)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1),(8,1)]
  | 37 => [(0,1),(6,5)]
  | 38 => [(0,4),(6,2)]
  | 39 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => [(4,0),(7,4),(8,0)]
  | 41 => [(1,3),(7,3)]
  | 42 => [(4,2),(8,2)]
  | 43 => [(5,0),(5,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5),(8,5)]
  | 48 => [(1,0),(3,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => [(0,1),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(6,2)]
  | 53 => [(1,4),(3,4),(5,4),(7,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(4,4),(7,2),(8,2)]
  | 59 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => [(0,3),(1,0),(3,0),(7,0)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(7,1)]
  | 68 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => [(0,0),(1,3),(1,4),(3,3),(6,4)]
  | 71 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 72 => [(2,0),(4,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2)]
  | 75 => [(5,0),(7,0),(8,0)]
  | 76 => [(4,3),(4,5),(7,3),(8,3)]
  | 77 => [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(7,5),(8,2)]
  | 78 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 79 => [(3,1),(5,1),(5,4),(8,4)]
  | 80 => [(0,1),(1,4)]
  | 81 => [(0,5),(6,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(1,4),(6,4),(7,4)]
  | 84 => [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => [(4,1),(4,5),(7,5),(8,5)]
  | 87 => [(0,2),(1,0),(6,0)]
  | 88 => [(1,1),(7,1)]
  | 89 => [(1,5),(4,1),(7,5),(8,1)]
  | _ => [(0,2),(0,3),(6,0),(6,1),(6,5)]
def root7Node2Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(7,2),(8,4)]
  | 1 => some [(1,4),(7,4)]
  | 2 => some [(0,5),(6,3)]
  | 3 => some [(2,0),(2,2),(2,4),(4,4)]
  | 4 => some [(0,0),(1,3),(3,3),(7,3)]
  | 5 => some [(3,2),(5,2),(7,2)]
  | 6 => some [(1,1),(7,1)]
  | 7 => some [(4,1),(7,5)]
  | 8 => some [(0,2),(6,0)]
  | 9 => some [(1,1),(3,1),(7,1)]
  | 10 => some [(0,1),(1,5),(6,5)]
  | 11 => some [(0,4),(6,1),(6,2)]
  | 12 => some [(5,1),(5,4),(8,4)]
  | 13 => some [(4,0),(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2),(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(5,1),(5,4),(8,4)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(4,2),(8,2)]
  | 30 => some [(4,3),(5,3),(7,1),(8,3)]
  | 31 => some [(7,5),(8,5)]
  | 32 => some [(0,3),(1,0)]
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
  | 53 => some [(1,4),(3,4),(5,4),(7,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => some [(0,3),(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(6,4)]
  | 71 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 72 => some [(2,0),(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(5,0),(7,0),(8,0)]
  | 76 => some [(4,3),(4,5),(7,3),(8,3)]
  | 77 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(7,5),(8,2)]
  | 78 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 79 => some [(3,1),(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4)]
  | 81 => some [(0,5),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(1,4),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => some [(1,1),(4,3),(5,0),(5,3),(6,1),(7,1),(8,3)]
  | 86 => some [(4,1),(4,5),(7,5),(8,5)]
  | 87 => some [(0,2),(1,0),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(1,5),(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(6,0),(6,1),(6,5)]
theorem root7Node2Domains2_fast_eq : root7Node2Domains2 = expandDomains root7Node2Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node2Domains2 v = expandDomains root7Node2Domains2Fast v from by decide) v
theorem root7Node2Step2Chunk0_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_0⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk0_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_1⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk0_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_2⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk0_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_3⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk0_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_4⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk0_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows0_5⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk1_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_0⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk1_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_1⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk1_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_2⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk1_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_3⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk1_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_4⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk1_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows1_5⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk2_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_0⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk2_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_1⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk2_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_2⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk2_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_3⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk2_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_4⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk2_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows2_5⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk3_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_0⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk3_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_1⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk3_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_2⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk3_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_3⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk3_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_4⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk3_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows3_5⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk4_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_0⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk4_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_1⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk4_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_2⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk4_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_3⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk4_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_4⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk4_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows4_5⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk5_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_0⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk5_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_1⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk5_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_2⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk5_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_3⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk5_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_4⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk5_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows5_5⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk6_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_0⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk6_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_1⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk6_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_2⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk6_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_3⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk6_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_4⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk6_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows6_5⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk7_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_0⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk7_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_1⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk7_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_2⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk7_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_3⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk7_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_4⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk7_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows7_5⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk8_0_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_0⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk8_1_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_1⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk8_2_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_2⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk8_3_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_3⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk8_4_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_4⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Chunk8_5_checked :
    checkNarrowing ⟨table4Scope, table4Rows8_5⟩
      root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq (by decide)
theorem root7Node2Step2Narrowing_checked :
    checkNarrowing table4 root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkNarrowing_flatten table4Scope [table4Rows0_0,table4Rows0_1,table4Rows0_2,table4Rows0_3,table4Rows0_4,table4Rows0_5,table4Rows1_0,table4Rows1_1,table4Rows1_2,table4Rows1_3,table4Rows1_4,table4Rows1_5,table4Rows2_0,table4Rows2_1,table4Rows2_2,table4Rows2_3,table4Rows2_4,table4Rows2_5,table4Rows3_0,table4Rows3_1,table4Rows3_2,table4Rows3_3,table4Rows3_4,table4Rows3_5,table4Rows4_0,table4Rows4_1,table4Rows4_2,table4Rows4_3,table4Rows4_4,table4Rows4_5,table4Rows5_0,table4Rows5_1,table4Rows5_2,table4Rows5_3,table4Rows5_4,table4Rows5_5,table4Rows6_0,table4Rows6_1,table4Rows6_2,table4Rows6_3,table4Rows6_4,table4Rows6_5,table4Rows7_0,table4Rows7_1,table4Rows7_2,table4Rows7_3,table4Rows7_4,table4Rows7_5,table4Rows8_0,table4Rows8_1,table4Rows8_2,table4Rows8_3,table4Rows8_4,table4Rows8_5]
    root7Node2Domains1 root7Node2Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node2Step2Chunk0_0_checked, root7Node2Step2Chunk0_1_checked, root7Node2Step2Chunk0_2_checked, root7Node2Step2Chunk0_3_checked, root7Node2Step2Chunk0_4_checked, root7Node2Step2Chunk0_5_checked, root7Node2Step2Chunk1_0_checked, root7Node2Step2Chunk1_1_checked, root7Node2Step2Chunk1_2_checked, root7Node2Step2Chunk1_3_checked, root7Node2Step2Chunk1_4_checked, root7Node2Step2Chunk1_5_checked, root7Node2Step2Chunk2_0_checked, root7Node2Step2Chunk2_1_checked, root7Node2Step2Chunk2_2_checked, root7Node2Step2Chunk2_3_checked, root7Node2Step2Chunk2_4_checked, root7Node2Step2Chunk2_5_checked, root7Node2Step2Chunk3_0_checked, root7Node2Step2Chunk3_1_checked, root7Node2Step2Chunk3_2_checked, root7Node2Step2Chunk3_3_checked, root7Node2Step2Chunk3_4_checked, root7Node2Step2Chunk3_5_checked, root7Node2Step2Chunk4_0_checked, root7Node2Step2Chunk4_1_checked, root7Node2Step2Chunk4_2_checked, root7Node2Step2Chunk4_3_checked, root7Node2Step2Chunk4_4_checked, root7Node2Step2Chunk4_5_checked, root7Node2Step2Chunk5_0_checked, root7Node2Step2Chunk5_1_checked, root7Node2Step2Chunk5_2_checked, root7Node2Step2Chunk5_3_checked, root7Node2Step2Chunk5_4_checked, root7Node2Step2Chunk5_5_checked, root7Node2Step2Chunk6_0_checked, root7Node2Step2Chunk6_1_checked, root7Node2Step2Chunk6_2_checked, root7Node2Step2Chunk6_3_checked, root7Node2Step2Chunk6_4_checked, root7Node2Step2Chunk6_5_checked, root7Node2Step2Chunk7_0_checked, root7Node2Step2Chunk7_1_checked, root7Node2Step2Chunk7_2_checked, root7Node2Step2Chunk7_3_checked, root7Node2Step2Chunk7_4_checked, root7Node2Step2Chunk7_5_checked, root7Node2Step2Chunk8_0_checked, root7Node2Step2Chunk8_1_checked, root7Node2Step2Chunk8_2_checked, root7Node2Step2Chunk8_3_checked, root7Node2Step2Chunk8_4_checked, root7Node2Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node2Step2_checked :
    checkReplacement table4 root7Node2Domains1 root7Node2Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node2Domains1 root7Node2Domains2
    root7Node2Domains1Fast root7Node2Domains2Fast
    root7Node2Domains1_fast_eq root7Node2Domains2_fast_eq
    root7Node2Step2Narrowing_checked (by decide)
def root7Node2Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(7,2),(8,4)]
  | 1 => [(1,4),(7,4)]
  | 2 => [(0,5),(6,3)]
  | 3 => [(2,0),(2,2),(2,4),(4,4)]
  | 4 => [(0,0),(1,3),(3,3),(7,3)]
  | 5 => [(3,2),(5,2),(7,2)]
  | 6 => [(1,1),(7,1)]
  | 7 => [(4,1),(7,5)]
  | 8 => [(0,2),(6,0)]
  | 9 => [(1,1),(3,1),(7,1)]
  | 10 => [(0,1),(1,5),(6,5)]
  | 11 => [(0,4),(6,1),(6,2)]
  | 12 => [(5,1),(5,4),(8,4)]
  | 13 => [(4,0),(8,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2),(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0),(7,0)]
  | 19 => [(4,3),(7,1),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(5,1),(5,4),(8,4)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(4,2),(8,2)]
  | 30 => [(4,3),(5,3),(7,1),(8,3)]
  | 31 => [(7,5),(8,5)]
  | 32 => [(0,3),(1,0)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1),(8,1)]
  | 37 => [(0,1),(6,5)]
  | 38 => [(0,4),(6,2)]
  | 39 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => [(4,0),(7,4),(8,0)]
  | 41 => [(1,3),(7,3)]
  | 42 => [(4,2),(8,2)]
  | 43 => [(5,0),(5,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5),(8,5)]
  | 48 => [(1,0),(3,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => [(0,1),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(6,2)]
  | 53 => [(1,4),(3,4),(5,4),(7,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(4,4),(7,2),(8,2)]
  | 59 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => [(0,3),(1,0),(3,0),(7,0)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(7,1)]
  | 68 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => [(0,0),(1,3),(1,4),(3,3),(6,4)]
  | 71 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 72 => [(2,0),(4,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2)]
  | 75 => [(5,0),(7,0),(8,0)]
  | 76 => [(4,3),(4,5),(7,3),(8,3)]
  | 77 => [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 78 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 79 => [(3,1),(5,1),(5,4),(8,4)]
  | 80 => [(0,1),(1,4)]
  | 81 => [(0,5),(6,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(1,4),(6,4)]
  | 84 => [(0,5),(1,2),(7,2)]
  | 85 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 86 => [(4,5),(7,5),(8,5)]
  | 87 => [(1,0),(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,0),(6,1)]
def root7Node2Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(7,2),(8,4)]
  | 1 => some [(1,4),(7,4)]
  | 2 => some [(0,5),(6,3)]
  | 3 => some [(2,0),(2,2),(2,4),(4,4)]
  | 4 => some [(0,0),(1,3),(3,3),(7,3)]
  | 5 => some [(3,2),(5,2),(7,2)]
  | 6 => some [(1,1),(7,1)]
  | 7 => some [(4,1),(7,5)]
  | 8 => some [(0,2),(6,0)]
  | 9 => some [(1,1),(3,1),(7,1)]
  | 10 => some [(0,1),(1,5),(6,5)]
  | 11 => some [(0,4),(6,1),(6,2)]
  | 12 => some [(5,1),(5,4),(8,4)]
  | 13 => some [(4,0),(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2),(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(5,1),(5,4),(8,4)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(4,2),(8,2)]
  | 30 => some [(4,3),(5,3),(7,1),(8,3)]
  | 31 => some [(7,5),(8,5)]
  | 32 => some [(0,3),(1,0)]
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
  | 53 => some [(1,4),(3,4),(5,4),(7,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => some [(0,3),(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(6,4)]
  | 71 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 72 => some [(2,0),(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(5,0),(7,0),(8,0)]
  | 76 => some [(4,3),(4,5),(7,3),(8,3)]
  | 77 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 78 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 79 => some [(3,1),(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4)]
  | 81 => some [(0,5),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(1,4),(6,4)]
  | 84 => some [(0,5),(1,2),(7,2)]
  | 85 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 86 => some [(4,5),(7,5),(8,5)]
  | 87 => some [(1,0),(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,0),(6,1)]
theorem root7Node2Domains3_fast_eq : root7Node2Domains3 = expandDomains root7Node2Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node2Domains3 v = expandDomains root7Node2Domains3Fast v from by decide) v
theorem root7Node2Step3Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq (by decide)
theorem root7Node2Step3Narrowing_checked :
    checkNarrowing table65 root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root7Node2Domains2 root7Node2Domains3 (by
      simp only [List.all_cons, List.all_nil, root7Node2Step3Chunk0_0_checked, root7Node2Step3Chunk0_1_checked, root7Node2Step3Chunk0_2_checked, root7Node2Step3Chunk0_3_checked, root7Node2Step3Chunk0_4_checked, root7Node2Step3Chunk0_5_checked, root7Node2Step3Chunk1_0_checked, root7Node2Step3Chunk1_1_checked, root7Node2Step3Chunk1_2_checked, root7Node2Step3Chunk1_3_checked, root7Node2Step3Chunk1_4_checked, root7Node2Step3Chunk1_5_checked, root7Node2Step3Chunk2_0_checked, root7Node2Step3Chunk2_1_checked, root7Node2Step3Chunk2_2_checked, root7Node2Step3Chunk2_3_checked, root7Node2Step3Chunk2_4_checked, root7Node2Step3Chunk2_5_checked, root7Node2Step3Chunk3_0_checked, root7Node2Step3Chunk3_1_checked, root7Node2Step3Chunk3_2_checked, root7Node2Step3Chunk3_3_checked, root7Node2Step3Chunk3_4_checked, root7Node2Step3Chunk3_5_checked, root7Node2Step3Chunk4_0_checked, root7Node2Step3Chunk4_1_checked, root7Node2Step3Chunk4_2_checked, root7Node2Step3Chunk4_3_checked, root7Node2Step3Chunk4_4_checked, root7Node2Step3Chunk4_5_checked, root7Node2Step3Chunk5_0_checked, root7Node2Step3Chunk5_1_checked, root7Node2Step3Chunk5_2_checked, root7Node2Step3Chunk5_3_checked, root7Node2Step3Chunk5_4_checked, root7Node2Step3Chunk5_5_checked, root7Node2Step3Chunk6_0_checked, root7Node2Step3Chunk6_1_checked, root7Node2Step3Chunk6_2_checked, root7Node2Step3Chunk6_3_checked, root7Node2Step3Chunk6_4_checked, root7Node2Step3Chunk6_5_checked, root7Node2Step3Chunk7_0_checked, root7Node2Step3Chunk7_1_checked, root7Node2Step3Chunk7_2_checked, root7Node2Step3Chunk7_3_checked, root7Node2Step3Chunk7_4_checked, root7Node2Step3Chunk7_5_checked, root7Node2Step3Chunk8_0_checked, root7Node2Step3Chunk8_1_checked, root7Node2Step3Chunk8_2_checked, root7Node2Step3Chunk8_3_checked, root7Node2Step3Chunk8_4_checked, root7Node2Step3Chunk8_5_checked, Bool.true_and])
theorem root7Node2Step3_checked :
    checkReplacement table65 root7Node2Domains2 root7Node2Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root7Node2Domains2 root7Node2Domains3
    root7Node2Domains2Fast root7Node2Domains3Fast
    root7Node2Domains2_fast_eq root7Node2Domains3_fast_eq
    root7Node2Step3Narrowing_checked (by decide)
def root7Node3Domains0 : Domains 91 State := restrict root7Node2Domains3 1 (1,4)
def root7Node3Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(7,2),(8,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5),(6,3)]
  | 3 => some [(2,0),(2,2),(2,4),(4,4)]
  | 4 => some [(0,0),(1,3),(3,3),(7,3)]
  | 5 => some [(3,2),(5,2),(7,2)]
  | 6 => some [(1,1),(7,1)]
  | 7 => some [(4,1),(7,5)]
  | 8 => some [(0,2),(6,0)]
  | 9 => some [(1,1),(3,1),(7,1)]
  | 10 => some [(0,1),(1,5),(6,5)]
  | 11 => some [(0,4),(6,1),(6,2)]
  | 12 => some [(5,1),(5,4),(8,4)]
  | 13 => some [(4,0),(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2),(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(5,1),(5,4),(8,4)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(4,2),(8,2)]
  | 30 => some [(4,3),(5,3),(7,1),(8,3)]
  | 31 => some [(7,5),(8,5)]
  | 32 => some [(0,3),(1,0)]
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
  | 53 => some [(1,4),(3,4),(5,4),(7,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => some [(0,3),(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(6,4)]
  | 71 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 72 => some [(2,0),(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(5,0),(7,0),(8,0)]
  | 76 => some [(4,3),(4,5),(7,3),(8,3)]
  | 77 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 78 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 79 => some [(3,1),(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4)]
  | 81 => some [(0,5),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(1,4),(6,4)]
  | 84 => some [(0,5),(1,2),(7,2)]
  | 85 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 86 => some [(4,5),(7,5),(8,5)]
  | 87 => some [(1,0),(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,0),(6,1)]
theorem root7Node3Domains0_fast_eq : root7Node3Domains0 = expandDomains root7Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node3Domains0 v = expandDomains root7Node3Domains0Fast v from by decide) v
def root7Node3Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(8,4)]
  | 1 => [(1,4)]
  | 2 => [(0,5)]
  | 3 => [(2,0),(2,4),(4,4)]
  | 4 => [(0,0),(1,3),(7,3)]
  | 5 => [(3,2),(5,2),(7,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(6,0)]
  | 9 => [(3,1),(7,1)]
  | 10 => [(0,1),(1,5),(6,5)]
  | 11 => [(0,4),(6,1),(6,2)]
  | 12 => [(5,1),(5,4),(8,4)]
  | 13 => [(4,0),(8,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,0),(7,0)]
  | 19 => [(4,3),(7,1),(8,3)]
  | 20 => [(7,5),(8,5)]
  | 21 => [(5,1),(5,4),(8,4)]
  | 22 => [(0,1),(6,4)]
  | 23 => [(1,2),(6,2)]
  | 24 => [(8,4)]
  | 25 => [(0,0)]
  | 26 => [(7,2)]
  | 27 => [(4,0),(7,4)]
  | 28 => [(1,3),(7,3)]
  | 29 => [(4,2),(8,2)]
  | 30 => [(4,3),(7,1),(8,3)]
  | 31 => [(7,5),(8,5)]
  | 32 => [(0,3),(1,0)]
  | 33 => [(7,1),(8,1)]
  | 34 => [(1,5)]
  | 35 => [(6,1)]
  | 36 => [(5,1),(8,1)]
  | 37 => [(0,1),(6,5)]
  | 38 => [(0,4),(6,2)]
  | 39 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 40 => [(4,0),(7,4),(8,0)]
  | 41 => [(1,3),(7,3)]
  | 42 => [(4,2),(8,2)]
  | 43 => [(5,0),(5,3)]
  | 44 => [(4,5),(5,5),(8,5)]
  | 45 => [(7,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5),(8,5)]
  | 48 => [(1,0),(3,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 50 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 51 => [(0,1),(6,4),(6,5)]
  | 52 => [(0,4),(1,2),(6,2)]
  | 53 => [(1,4),(3,4),(5,4),(7,4)]
  | 54 => [(0,0),(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(1,4),(7,4)]
  | 57 => [(0,5),(1,3),(6,3)]
  | 58 => [(4,4),(7,2),(8,2)]
  | 59 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => [(0,3),(1,0),(3,0),(7,0)]
  | 62 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 63 => [(0,2),(1,5),(6,0)]
  | 64 => [(1,1),(6,1),(7,1)]
  | 65 => [(4,1),(7,5),(8,1)]
  | 66 => [(0,2),(6,0),(6,5)]
  | 67 => [(0,4),(1,1),(7,1)]
  | 68 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => [(0,0),(1,3),(1,4),(3,3),(6,4)]
  | 71 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 72 => [(2,0),(4,0),(8,0)]
  | 73 => [(7,3),(8,3)]
  | 74 => [(5,2),(5,5),(8,2)]
  | 75 => [(5,0),(7,0),(8,0)]
  | 76 => [(4,3),(4,5),(7,3),(8,3)]
  | 77 => [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 78 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 79 => [(3,1),(5,1),(5,4),(8,4)]
  | 80 => [(0,1),(1,4)]
  | 81 => [(0,5),(6,2)]
  | 82 => [(4,4),(8,4)]
  | 83 => [(0,0),(1,4),(6,4)]
  | 84 => [(0,5),(1,2),(7,2)]
  | 85 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 86 => [(4,5),(7,5),(8,5)]
  | 87 => [(1,0),(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,0),(6,1)]
def root7Node3Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(8,4)]
  | 1 => some [(1,4)]
  | 2 => some [(0,5)]
  | 3 => some [(2,0),(2,4),(4,4)]
  | 4 => some [(0,0),(1,3),(7,3)]
  | 5 => some [(3,2),(5,2),(7,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(6,0)]
  | 9 => some [(3,1),(7,1)]
  | 10 => some [(0,1),(1,5),(6,5)]
  | 11 => some [(0,4),(6,1),(6,2)]
  | 12 => some [(5,1),(5,4),(8,4)]
  | 13 => some [(4,0),(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,0),(7,0)]
  | 19 => some [(4,3),(7,1),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(5,1),(5,4),(8,4)]
  | 22 => some [(0,1),(6,4)]
  | 23 => some [(1,2),(6,2)]
  | 24 => some [(8,4)]
  | 25 => some [(0,0)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(7,4)]
  | 28 => some [(1,3),(7,3)]
  | 29 => some [(4,2),(8,2)]
  | 30 => some [(4,3),(7,1),(8,3)]
  | 31 => some [(7,5),(8,5)]
  | 32 => some [(0,3),(1,0)]
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
  | 53 => some [(1,4),(3,4),(5,4),(7,4)]
  | 54 => some [(0,0),(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(1,4),(7,4)]
  | 57 => some [(0,5),(1,3),(6,3)]
  | 58 => some [(4,4),(7,2),(8,2)]
  | 59 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 60 => some [(0,5),(1,2),(1,3),(3,2),(4,5),(6,3),(7,2),(7,3)]
  | 61 => some [(0,3),(1,0),(3,0),(7,0)]
  | 62 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 63 => some [(0,2),(1,5),(6,0)]
  | 64 => some [(1,1),(6,1),(7,1)]
  | 65 => some [(4,1),(7,5),(8,1)]
  | 66 => some [(0,2),(6,0),(6,5)]
  | 67 => some [(0,4),(1,1),(7,1)]
  | 68 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 69 => some [(0,0),(0,1),(0,2),(0,3),(6,0),(6,1),(6,4),(6,5)]
  | 70 => some [(0,0),(1,3),(1,4),(3,3),(6,4)]
  | 71 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 72 => some [(2,0),(4,0),(8,0)]
  | 73 => some [(7,3),(8,3)]
  | 74 => some [(5,2),(5,5),(8,2)]
  | 75 => some [(5,0),(7,0),(8,0)]
  | 76 => some [(4,3),(4,5),(7,3),(8,3)]
  | 77 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 78 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 79 => some [(3,1),(5,1),(5,4),(8,4)]
  | 80 => some [(0,1),(1,4)]
  | 81 => some [(0,5),(6,2)]
  | 82 => some [(4,4),(8,4)]
  | 83 => some [(0,0),(1,4),(6,4)]
  | 84 => some [(0,5),(1,2),(7,2)]
  | 85 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 86 => some [(4,5),(7,5),(8,5)]
  | 87 => some [(1,0),(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,0),(6,1)]
theorem root7Node3Domains1_fast_eq : root7Node3Domains1 = expandDomains root7Node3Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node3Domains1 v = expandDomains root7Node3Domains1Fast v from by decide) v
theorem root7Node3Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq (by decide)
theorem root7Node3Step1Narrowing_checked :
    checkNarrowing table0 root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkNarrowing_flatten table0Scope [table0Rows0_0,table0Rows0_1,table0Rows0_2,table0Rows0_3,table0Rows0_4,table0Rows0_5,table0Rows1_0,table0Rows1_1,table0Rows1_2,table0Rows1_3,table0Rows1_4,table0Rows1_5,table0Rows2_0,table0Rows2_1,table0Rows2_2,table0Rows2_3,table0Rows2_4,table0Rows2_5,table0Rows3_0,table0Rows3_1,table0Rows3_2,table0Rows3_3,table0Rows3_4,table0Rows3_5,table0Rows4_0,table0Rows4_1,table0Rows4_2,table0Rows4_3,table0Rows4_4,table0Rows4_5,table0Rows5_0,table0Rows5_1,table0Rows5_2,table0Rows5_3,table0Rows5_4,table0Rows5_5,table0Rows6_0,table0Rows6_1,table0Rows6_2,table0Rows6_3,table0Rows6_4,table0Rows6_5,table0Rows7_0,table0Rows7_1,table0Rows7_2,table0Rows7_3,table0Rows7_4,table0Rows7_5,table0Rows8_0,table0Rows8_1,table0Rows8_2,table0Rows8_3,table0Rows8_4,table0Rows8_5]
    root7Node3Domains0 root7Node3Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node3Step1Chunk0_0_checked, root7Node3Step1Chunk0_1_checked, root7Node3Step1Chunk0_2_checked, root7Node3Step1Chunk0_3_checked, root7Node3Step1Chunk0_4_checked, root7Node3Step1Chunk0_5_checked, root7Node3Step1Chunk1_0_checked, root7Node3Step1Chunk1_1_checked, root7Node3Step1Chunk1_2_checked, root7Node3Step1Chunk1_3_checked, root7Node3Step1Chunk1_4_checked, root7Node3Step1Chunk1_5_checked, root7Node3Step1Chunk2_0_checked, root7Node3Step1Chunk2_1_checked, root7Node3Step1Chunk2_2_checked, root7Node3Step1Chunk2_3_checked, root7Node3Step1Chunk2_4_checked, root7Node3Step1Chunk2_5_checked, root7Node3Step1Chunk3_0_checked, root7Node3Step1Chunk3_1_checked, root7Node3Step1Chunk3_2_checked, root7Node3Step1Chunk3_3_checked, root7Node3Step1Chunk3_4_checked, root7Node3Step1Chunk3_5_checked, root7Node3Step1Chunk4_0_checked, root7Node3Step1Chunk4_1_checked, root7Node3Step1Chunk4_2_checked, root7Node3Step1Chunk4_3_checked, root7Node3Step1Chunk4_4_checked, root7Node3Step1Chunk4_5_checked, root7Node3Step1Chunk5_0_checked, root7Node3Step1Chunk5_1_checked, root7Node3Step1Chunk5_2_checked, root7Node3Step1Chunk5_3_checked, root7Node3Step1Chunk5_4_checked, root7Node3Step1Chunk5_5_checked, root7Node3Step1Chunk6_0_checked, root7Node3Step1Chunk6_1_checked, root7Node3Step1Chunk6_2_checked, root7Node3Step1Chunk6_3_checked, root7Node3Step1Chunk6_4_checked, root7Node3Step1Chunk6_5_checked, root7Node3Step1Chunk7_0_checked, root7Node3Step1Chunk7_1_checked, root7Node3Step1Chunk7_2_checked, root7Node3Step1Chunk7_3_checked, root7Node3Step1Chunk7_4_checked, root7Node3Step1Chunk7_5_checked, root7Node3Step1Chunk8_0_checked, root7Node3Step1Chunk8_1_checked, root7Node3Step1Chunk8_2_checked, root7Node3Step1Chunk8_3_checked, root7Node3Step1Chunk8_4_checked, root7Node3Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node3Step1_checked :
    checkReplacement table0 root7Node3Domains0 root7Node3Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node3Domains0 root7Node3Domains1
    root7Node3Domains0Fast root7Node3Domains1Fast
    root7Node3Domains0_fast_eq root7Node3Domains1_fast_eq
    root7Node3Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
