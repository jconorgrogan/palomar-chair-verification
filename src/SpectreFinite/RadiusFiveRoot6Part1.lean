module

public import SpectreFinite.RadiusFiveRoot6Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable25
public import SpectreFinite.RadiusFiveTable55
public import SpectreFinite.RadiusFiveTable57
public import SpectreFinite.RadiusFiveTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node1Domains0 : Domains 91 State := restrict root6Node0Domains4 44 (2,5)
def root6Node1Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(5,2),(7,0),(8,2)]
  | 1 => some [(4,3),(5,0),(5,3),(8,0),(8,3)]
  | 2 => some [(4,5),(7,3),(7,5),(8,5)]
  | 3 => some [(1,0),(4,2),(5,2),(6,0),(7,0),(8,2)]
  | 4 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 5 => some [(1,5),(4,5),(7,5),(8,5)]
  | 6 => some [(0,4),(1,2),(7,2)]
  | 7 => some [(5,4),(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(6,3),(6,4)]
  | 9 => some [(1,2),(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(7,4),(8,0),(8,4)]
  | 11 => some [(0,0),(1,3),(4,5),(7,3)]
  | 12 => some [(4,2),(7,0),(7,2),(8,2)]
  | 13 => some [(0,3),(1,1),(6,1),(7,0)]
  | 14 => some [(4,1),(4,3),(8,1)]
  | 15 => some [(0,2),(1,5),(6,5),(7,5)]
  | 16 => some [(0,3),(0,4),(1,1),(6,1)]
  | 17 => some [(5,1),(5,4),(8,1)]
  | 18 => some [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 19 => some [(0,4),(1,2),(6,1),(6,2),(7,2)]
  | 20 => some [(1,4),(3,4),(5,1),(5,4),(7,4),(8,1)]
  | 21 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(7,0),(7,2),(8,0)]
  | 22 => some [(1,3),(3,3),(5,3),(7,3),(7,4),(8,3)]
  | 23 => some [(1,3),(5,2),(5,5)]
  | 24 => some [(4,2),(7,0),(8,0)]
  | 25 => some [(4,3),(5,3),(8,3)]
  | 26 => some [(1,5),(3,5),(5,5)]
  | 27 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 28 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(8,3)]
  | 29 => some [(0,2),(1,5),(3,5),(5,5),(6,0)]
  | 30 => some [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(6,1),(7,1),(8,4)]
  | 31 => some [(0,1),(1,4),(6,5),(8,1)]
  | 32 => some [(0,4),(0,5),(6,2),(6,5)]
  | 33 => some [(0,4),(4,4),(5,4),(8,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(2,0),(2,4),(4,4)]
  | 37 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 38 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => some [(2,0),(2,4),(4,0),(4,4),(8,0)]
  | 40 => some [(3,0),(4,3),(5,0),(5,3),(7,0),(7,1),(8,0),(8,3)]
  | 41 => some [(2,5),(4,5),(7,5),(8,3),(8,5)]
  | 42 => some [(1,0),(5,5),(6,0),(7,0)]
  | 43 => some [(3,0),(4,3),(7,1)]
  | 44 => some [(2,5)]
  | 45 => some [(6,0)]
  | 46 => some [(3,1),(7,1)]
  | 47 => some [(0,1),(1,5),(6,5),(7,5)]
  | 48 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 49 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => some [(0,1),(1,4),(1,5),(6,4),(6,5),(7,5)]
  | 51 => some [(0,0),(1,3),(1,4),(7,3)]
  | 52 => some [(0,5),(7,2),(8,2)]
  | 53 => some [(4,0),(4,4),(7,4),(8,0)]
  | 54 => some [(0,0),(1,3),(7,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(1,0),(4,2),(7,0),(8,2)]
  | 59 => some [(4,3),(5,0),(5,3),(7,1),(8,0),(8,3)]
  | 60 => some [(4,5),(7,3),(7,5),(8,5)]
  | 61 => some [(0,4),(6,0),(6,1),(6,2)]
  | 62 => some [(5,1),(5,4),(7,1),(8,1),(8,4)]
  | 63 => some [(0,1),(1,5),(6,4),(6,5)]
  | 64 => some [(0,4),(1,2),(6,1),(6,2)]
  | 65 => some [(5,1),(5,4),(8,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(4,0),(7,4),(8,4)]
  | 69 => some [(0,0),(1,3),(6,3),(6,4),(7,3)]
  | 70 => some [(4,3),(5,0),(7,1),(8,3)]
  | 71 => some [(4,5),(5,5),(7,5),(8,5)]
  | 72 => some [(0,3),(1,0),(7,0)]
  | 73 => some [(4,3),(7,1),(8,1),(8,3)]
  | 74 => some [(1,5),(3,5),(7,5),(8,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(4,1),(5,1),(7,1),(8,1)]
  | 77 => some [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 78 => some [(0,0),(0,5),(1,3),(6,3),(7,3)]
  | 79 => some [(4,2),(4,4),(7,2),(8,2)]
  | 80 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 81 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(7,0),(7,2),(8,2)]
  | 83 => some [(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0),(8,3)]
  | 84 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 85 => some [(0,4),(1,1),(1,2),(6,1),(6,2),(7,1)]
  | 86 => some [(1,4),(3,4),(4,1),(5,1),(5,4),(7,4),(7,5),(8,1)]
  | 87 => some [(0,0),(0,1),(0,2),(0,5),(6,0),(6,3),(6,4),(6,5)]
  | 88 => some [(0,4),(1,1),(1,2),(3,1),(4,4),(6,2),(7,1),(7,2)]
  | 89 => some [(0,1),(1,4),(3,4),(5,1),(5,4),(6,5),(7,4)]
  | _ => some [(0,0),(0,1),(0,4),(0,5),(1,3),(6,2),(6,3),(6,4)]
theorem root6Node1Domains0_fast_eq : root6Node1Domains0 = expandDomains root6Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node1Domains0 v = expandDomains root6Node1Domains0Fast v from by decide) v
def root6Node1Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,2),(5,2),(7,0),(8,2)]
  | 1 => [(4,3),(5,0),(5,3),(8,0),(8,3)]
  | 2 => [(4,5),(7,3),(7,5),(8,5)]
  | 3 => [(1,0),(4,2),(5,2),(6,0),(7,0),(8,2)]
  | 4 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 5 => [(1,5),(4,5),(7,5),(8,5)]
  | 6 => [(0,4),(1,2),(7,2)]
  | 7 => [(5,4),(7,4),(8,4)]
  | 8 => [(0,0),(1,3),(6,3),(6,4)]
  | 9 => [(1,2),(7,2),(8,2)]
  | 10 => [(4,0),(5,0),(7,4),(8,0),(8,4)]
  | 11 => [(0,0),(1,3),(4,5),(7,3)]
  | 12 => [(4,2),(7,0),(7,2),(8,2)]
  | 13 => [(0,3),(1,1),(6,1),(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(8,1)]
  | 18 => [(1,5),(6,5)]
  | 19 => [(0,4),(1,2),(6,1),(6,2),(7,2)]
  | 20 => [(1,4),(3,4),(5,1),(5,4),(7,4),(8,1)]
  | 21 => [(2,0),(2,2),(2,4),(4,0),(4,2),(7,0),(7,2),(8,0)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(4,2)]
  | 25 => [(5,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(2,1),(2,3),(2,5),(4,1),(4,3),(8,3)]
  | 29 => [(0,2),(1,5),(3,5),(5,5),(6,0)]
  | 30 => [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(6,1),(7,1),(8,4)]
  | 31 => [(8,1)]
  | 32 => [(6,5)]
  | 33 => [(0,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => [(2,0),(2,4),(4,0),(4,4),(8,0)]
  | 40 => [(3,0),(4,3),(5,0),(5,3),(7,0),(7,1),(8,0),(8,3)]
  | 41 => [(8,3)]
  | 42 => [(5,5)]
  | 43 => [(3,0)]
  | 44 => [(2,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => [(0,1),(1,4),(1,5),(6,4),(6,5),(7,5)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0),(8,0)]
  | 60 => [(4,5),(7,3),(7,5),(8,5)]
  | 61 => [(6,0)]
  | 62 => [(7,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0),(1,3),(6,3),(6,4),(7,3)]
  | 70 => [(5,0)]
  | 71 => [(4,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 78 => [(0,0)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3),(6,3)]
  | 82 => [(7,2),(8,2)]
  | 83 => [(4,0),(5,0),(8,0)]
  | 84 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 85 => [(6,1)]
  | 86 => [(4,1),(8,1)]
  | 87 => [(0,2),(6,5)]
  | 88 => [(0,4),(1,1)]
  | 89 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(0,4),(0,5),(1,3),(6,2),(6,3),(6,4)]
def root6Node1Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,2),(5,2),(7,0),(8,2)]
  | 1 => some [(4,3),(5,0),(5,3),(8,0),(8,3)]
  | 2 => some [(4,5),(7,3),(7,5),(8,5)]
  | 3 => some [(1,0),(4,2),(5,2),(6,0),(7,0),(8,2)]
  | 4 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 5 => some [(1,5),(4,5),(7,5),(8,5)]
  | 6 => some [(0,4),(1,2),(7,2)]
  | 7 => some [(5,4),(7,4),(8,4)]
  | 8 => some [(0,0),(1,3),(6,3),(6,4)]
  | 9 => some [(1,2),(7,2),(8,2)]
  | 10 => some [(4,0),(5,0),(7,4),(8,0),(8,4)]
  | 11 => some [(0,0),(1,3),(4,5),(7,3)]
  | 12 => some [(4,2),(7,0),(7,2),(8,2)]
  | 13 => some [(0,3),(1,1),(6,1),(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(8,1)]
  | 18 => some [(1,5),(6,5)]
  | 19 => some [(0,4),(1,2),(6,1),(6,2),(7,2)]
  | 20 => some [(1,4),(3,4),(5,1),(5,4),(7,4),(8,1)]
  | 21 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(7,0),(7,2),(8,0)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(4,2)]
  | 25 => some [(5,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(8,3)]
  | 29 => some [(0,2),(1,5),(3,5),(5,5),(6,0)]
  | 30 => some [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(6,1),(7,1),(8,4)]
  | 31 => some [(8,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 39 => some [(2,0),(2,4),(4,0),(4,4),(8,0)]
  | 40 => some [(3,0),(4,3),(5,0),(5,3),(7,0),(7,1),(8,0),(8,3)]
  | 41 => some [(8,3)]
  | 42 => some [(5,5)]
  | 43 => some [(3,0)]
  | 44 => some [(2,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => some [(0,1),(1,4),(1,5),(6,4),(6,5),(7,5)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3),(7,5),(8,5)]
  | 61 => some [(6,0)]
  | 62 => some [(7,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0),(1,3),(6,3),(6,4),(7,3)]
  | 70 => some [(5,0)]
  | 71 => some [(4,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 78 => some [(0,0)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3),(6,3)]
  | 82 => some [(7,2),(8,2)]
  | 83 => some [(4,0),(5,0),(8,0)]
  | 84 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 85 => some [(6,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(0,2),(6,5)]
  | 88 => some [(0,4),(1,1)]
  | 89 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(0,4),(0,5),(1,3),(6,2),(6,3),(6,4)]
theorem root6Node1Domains1_fast_eq : root6Node1Domains1 = expandDomains root6Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node1Domains1 v = expandDomains root6Node1Domains1Fast v from by decide) v
theorem root6Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq (by decide)
theorem root6Node1Step1Narrowing_checked :
    checkNarrowing table55 root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root6Node1Domains0 root6Node1Domains1 (by
      simp only [List.all_cons, List.all_nil, root6Node1Step1Chunk0_0_checked, root6Node1Step1Chunk0_1_checked, root6Node1Step1Chunk0_2_checked, root6Node1Step1Chunk0_3_checked, root6Node1Step1Chunk0_4_checked, root6Node1Step1Chunk0_5_checked, root6Node1Step1Chunk1_0_checked, root6Node1Step1Chunk1_1_checked, root6Node1Step1Chunk1_2_checked, root6Node1Step1Chunk1_3_checked, root6Node1Step1Chunk1_4_checked, root6Node1Step1Chunk1_5_checked, root6Node1Step1Chunk2_0_checked, root6Node1Step1Chunk2_1_checked, root6Node1Step1Chunk2_2_checked, root6Node1Step1Chunk2_3_checked, root6Node1Step1Chunk2_4_checked, root6Node1Step1Chunk2_5_checked, root6Node1Step1Chunk3_0_checked, root6Node1Step1Chunk3_1_checked, root6Node1Step1Chunk3_2_checked, root6Node1Step1Chunk3_3_checked, root6Node1Step1Chunk3_4_checked, root6Node1Step1Chunk3_5_checked, root6Node1Step1Chunk4_0_checked, root6Node1Step1Chunk4_1_checked, root6Node1Step1Chunk4_2_checked, root6Node1Step1Chunk4_3_checked, root6Node1Step1Chunk4_4_checked, root6Node1Step1Chunk4_5_checked, root6Node1Step1Chunk5_0_checked, root6Node1Step1Chunk5_1_checked, root6Node1Step1Chunk5_2_checked, root6Node1Step1Chunk5_3_checked, root6Node1Step1Chunk5_4_checked, root6Node1Step1Chunk5_5_checked, root6Node1Step1Chunk6_0_checked, root6Node1Step1Chunk6_1_checked, root6Node1Step1Chunk6_2_checked, root6Node1Step1Chunk6_3_checked, root6Node1Step1Chunk6_4_checked, root6Node1Step1Chunk6_5_checked, root6Node1Step1Chunk7_0_checked, root6Node1Step1Chunk7_1_checked, root6Node1Step1Chunk7_2_checked, root6Node1Step1Chunk7_3_checked, root6Node1Step1Chunk7_4_checked, root6Node1Step1Chunk7_5_checked, root6Node1Step1Chunk8_0_checked, root6Node1Step1Chunk8_1_checked, root6Node1Step1Chunk8_2_checked, root6Node1Step1Chunk8_3_checked, root6Node1Step1Chunk8_4_checked, root6Node1Step1Chunk8_5_checked, Bool.true_and])
theorem root6Node1Step1_checked :
    checkReplacement table55 root6Node1Domains0 root6Node1Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root6Node1Domains0 root6Node1Domains1
    root6Node1Domains0Fast root6Node1Domains1Fast
    root6Node1Domains0_fast_eq root6Node1Domains1_fast_eq
    root6Node1Step1Narrowing_checked (by decide)
def root6Node1Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,2),(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2),(5,2),(8,2)]
  | 4 => [(5,0),(5,3)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4),(8,4)]
  | 11 => [(0,0),(1,3)]
  | 12 => [(7,2),(8,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(8,1)]
  | 18 => [(1,5),(6,5)]
  | 19 => [(0,4),(6,1)]
  | 20 => [(5,1),(5,4),(8,1)]
  | 21 => [(7,2)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(4,2)]
  | 25 => [(5,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3),(8,3)]
  | 29 => [(1,5),(3,5),(5,5)]
  | 30 => [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(6,1),(7,1),(8,4)]
  | 31 => [(8,1)]
  | 32 => [(6,5)]
  | 33 => [(0,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0),(2,4),(4,0),(4,4),(8,0)]
  | 40 => [(3,0),(4,3),(5,0),(5,3),(7,0),(7,1),(8,0),(8,3)]
  | 41 => [(8,3)]
  | 42 => [(5,5)]
  | 43 => [(3,0)]
  | 44 => [(2,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => [(0,1),(1,4),(1,5),(6,4),(6,5),(7,5)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0),(8,0)]
  | 60 => [(4,5),(7,3),(7,5),(8,5)]
  | 61 => [(6,0)]
  | 62 => [(7,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0),(1,3),(6,3),(6,4),(7,3)]
  | 70 => [(5,0)]
  | 71 => [(4,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 78 => [(0,0)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3),(6,3)]
  | 82 => [(7,2),(8,2)]
  | 83 => [(4,0),(5,0),(8,0)]
  | 84 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 85 => [(6,1)]
  | 86 => [(4,1),(8,1)]
  | 87 => [(0,2),(6,5)]
  | 88 => [(0,4),(1,1)]
  | 89 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(0,4),(0,5),(1,3),(6,2),(6,3),(6,4)]
def root6Node1Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2),(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2),(5,2),(8,2)]
  | 4 => some [(5,0),(5,3)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4),(8,4)]
  | 11 => some [(0,0),(1,3)]
  | 12 => some [(7,2),(8,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(8,1)]
  | 18 => some [(1,5),(6,5)]
  | 19 => some [(0,4),(6,1)]
  | 20 => some [(5,1),(5,4),(8,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(4,2)]
  | 25 => some [(5,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3),(8,3)]
  | 29 => some [(1,5),(3,5),(5,5)]
  | 30 => some [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(6,1),(7,1),(8,4)]
  | 31 => some [(8,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4),(4,0),(4,4),(8,0)]
  | 40 => some [(3,0),(4,3),(5,0),(5,3),(7,0),(7,1),(8,0),(8,3)]
  | 41 => some [(8,3)]
  | 42 => some [(5,5)]
  | 43 => some [(3,0)]
  | 44 => some [(2,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 50 => some [(0,1),(1,4),(1,5),(6,4),(6,5),(7,5)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3),(7,5),(8,5)]
  | 61 => some [(6,0)]
  | 62 => some [(7,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0),(1,3),(6,3),(6,4),(7,3)]
  | 70 => some [(5,0)]
  | 71 => some [(4,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(0,1),(0,2),(1,5),(6,5),(7,5)]
  | 78 => some [(0,0)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3),(6,3)]
  | 82 => some [(7,2),(8,2)]
  | 83 => some [(4,0),(5,0),(8,0)]
  | 84 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 85 => some [(6,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(0,2),(6,5)]
  | 88 => some [(0,4),(1,1)]
  | 89 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(0,4),(0,5),(1,3),(6,2),(6,3),(6,4)]
theorem root6Node1Domains2_fast_eq : root6Node1Domains2 = expandDomains root6Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node1Domains2 v = expandDomains root6Node1Domains2Fast v from by decide) v
theorem root6Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Narrowing_checked :
    checkNarrowing table25 root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_flatten table25Scope [table25Rows0_0,table25Rows0_1,table25Rows0_2,table25Rows0_3,table25Rows0_4,table25Rows0_5,table25Rows1_0,table25Rows1_1,table25Rows1_2,table25Rows1_3,table25Rows1_4,table25Rows1_5,table25Rows2_0,table25Rows2_1,table25Rows2_2,table25Rows2_3,table25Rows2_4,table25Rows2_5,table25Rows3_0,table25Rows3_1,table25Rows3_2,table25Rows3_3,table25Rows3_4,table25Rows3_5,table25Rows4_0,table25Rows4_1,table25Rows4_2,table25Rows4_3,table25Rows4_4,table25Rows4_5,table25Rows5_0,table25Rows5_1,table25Rows5_2,table25Rows5_3,table25Rows5_4,table25Rows5_5,table25Rows6_0,table25Rows6_1,table25Rows6_2,table25Rows6_3,table25Rows6_4,table25Rows6_5,table25Rows7_0,table25Rows7_1,table25Rows7_2,table25Rows7_3,table25Rows7_4,table25Rows7_5,table25Rows8_0,table25Rows8_1,table25Rows8_2,table25Rows8_3,table25Rows8_4,table25Rows8_5]
    root6Node1Domains1 root6Node1Domains2 (by
      simp only [List.all_cons, List.all_nil, root6Node1Step2Chunk0_0_checked, root6Node1Step2Chunk0_1_checked, root6Node1Step2Chunk0_2_checked, root6Node1Step2Chunk0_3_checked, root6Node1Step2Chunk0_4_checked, root6Node1Step2Chunk0_5_checked, root6Node1Step2Chunk1_0_checked, root6Node1Step2Chunk1_1_checked, root6Node1Step2Chunk1_2_checked, root6Node1Step2Chunk1_3_checked, root6Node1Step2Chunk1_4_checked, root6Node1Step2Chunk1_5_checked, root6Node1Step2Chunk2_0_checked, root6Node1Step2Chunk2_1_checked, root6Node1Step2Chunk2_2_checked, root6Node1Step2Chunk2_3_checked, root6Node1Step2Chunk2_4_checked, root6Node1Step2Chunk2_5_checked, root6Node1Step2Chunk3_0_checked, root6Node1Step2Chunk3_1_checked, root6Node1Step2Chunk3_2_checked, root6Node1Step2Chunk3_3_checked, root6Node1Step2Chunk3_4_checked, root6Node1Step2Chunk3_5_checked, root6Node1Step2Chunk4_0_checked, root6Node1Step2Chunk4_1_checked, root6Node1Step2Chunk4_2_checked, root6Node1Step2Chunk4_3_checked, root6Node1Step2Chunk4_4_checked, root6Node1Step2Chunk4_5_checked, root6Node1Step2Chunk5_0_checked, root6Node1Step2Chunk5_1_checked, root6Node1Step2Chunk5_2_checked, root6Node1Step2Chunk5_3_checked, root6Node1Step2Chunk5_4_checked, root6Node1Step2Chunk5_5_checked, root6Node1Step2Chunk6_0_checked, root6Node1Step2Chunk6_1_checked, root6Node1Step2Chunk6_2_checked, root6Node1Step2Chunk6_3_checked, root6Node1Step2Chunk6_4_checked, root6Node1Step2Chunk6_5_checked, root6Node1Step2Chunk7_0_checked, root6Node1Step2Chunk7_1_checked, root6Node1Step2Chunk7_2_checked, root6Node1Step2Chunk7_3_checked, root6Node1Step2Chunk7_4_checked, root6Node1Step2Chunk7_5_checked, root6Node1Step2Chunk8_0_checked, root6Node1Step2Chunk8_1_checked, root6Node1Step2Chunk8_2_checked, root6Node1Step2Chunk8_3_checked, root6Node1Step2Chunk8_4_checked, root6Node1Step2Chunk8_5_checked, Bool.true_and])
theorem root6Node1Step2_checked :
    checkReplacement table25 root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq
    root6Node1Step2Narrowing_checked (by decide)
def root6Node1Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,2),(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2),(5,2),(8,2)]
  | 4 => [(5,0),(5,3)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4),(8,4)]
  | 11 => [(0,0),(1,3)]
  | 12 => [(7,2),(8,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(8,1)]
  | 18 => [(1,5),(6,5)]
  | 19 => [(0,4),(6,1)]
  | 20 => [(5,1),(5,4),(8,1)]
  | 21 => [(7,2)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(4,2)]
  | 25 => [(5,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3),(8,3)]
  | 29 => [(1,5),(3,5),(5,5)]
  | 30 => [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(6,1),(7,1),(8,4)]
  | 31 => [(8,1)]
  | 32 => [(6,5)]
  | 33 => [(0,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0),(2,4),(4,4)]
  | 40 => [(3,0),(4,3),(5,0),(5,3),(7,0),(7,1),(8,0),(8,3)]
  | 41 => [(8,3)]
  | 42 => [(5,5)]
  | 43 => [(3,0)]
  | 44 => [(2,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1),(7,1)]
  | 50 => [(0,1),(1,5),(6,5),(7,5)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0),(8,0)]
  | 60 => [(4,5),(7,3)]
  | 61 => [(6,0)]
  | 62 => [(7,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0),(6,4)]
  | 70 => [(5,0)]
  | 71 => [(4,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(1,5),(7,5)]
  | 78 => [(0,0)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3),(6,3)]
  | 82 => [(7,2),(8,2)]
  | 83 => [(4,0),(5,0),(8,0)]
  | 84 => [(4,5),(7,3)]
  | 85 => [(6,1)]
  | 86 => [(4,1),(8,1)]
  | 87 => [(0,2),(6,5)]
  | 88 => [(0,4),(1,1)]
  | 89 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,4)]
def root6Node1Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2),(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2),(5,2),(8,2)]
  | 4 => some [(5,0),(5,3)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4),(8,4)]
  | 11 => some [(0,0),(1,3)]
  | 12 => some [(7,2),(8,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(8,1)]
  | 18 => some [(1,5),(6,5)]
  | 19 => some [(0,4),(6,1)]
  | 20 => some [(5,1),(5,4),(8,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(4,2)]
  | 25 => some [(5,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3),(8,3)]
  | 29 => some [(1,5),(3,5),(5,5)]
  | 30 => some [(0,4),(1,1),(3,1),(4,4),(5,1),(5,4),(6,1),(7,1),(8,4)]
  | 31 => some [(8,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4),(4,4)]
  | 40 => some [(3,0),(4,3),(5,0),(5,3),(7,0),(7,1),(8,0),(8,3)]
  | 41 => some [(8,3)]
  | 42 => some [(5,5)]
  | 43 => some [(3,0)]
  | 44 => some [(2,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(1,5),(6,5),(7,5)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(6,0)]
  | 62 => some [(7,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(5,0)]
  | 71 => some [(4,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(1,5),(7,5)]
  | 78 => some [(0,0)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3),(6,3)]
  | 82 => some [(7,2),(8,2)]
  | 83 => some [(4,0),(5,0),(8,0)]
  | 84 => some [(4,5),(7,3)]
  | 85 => some [(6,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(0,2),(6,5)]
  | 88 => some [(0,4),(1,1)]
  | 89 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root6Node1Domains3_fast_eq : root6Node1Domains3 = expandDomains root6Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node1Domains3 v = expandDomains root6Node1Domains3Fast v from by decide) v
theorem root6Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Narrowing_checked :
    checkNarrowing table57 root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root6Node1Domains2 root6Node1Domains3 (by
      simp only [List.all_cons, List.all_nil, root6Node1Step3Chunk0_0_checked, root6Node1Step3Chunk0_1_checked, root6Node1Step3Chunk0_2_checked, root6Node1Step3Chunk0_3_checked, root6Node1Step3Chunk0_4_checked, root6Node1Step3Chunk0_5_checked, root6Node1Step3Chunk1_0_checked, root6Node1Step3Chunk1_1_checked, root6Node1Step3Chunk1_2_checked, root6Node1Step3Chunk1_3_checked, root6Node1Step3Chunk1_4_checked, root6Node1Step3Chunk1_5_checked, root6Node1Step3Chunk2_0_checked, root6Node1Step3Chunk2_1_checked, root6Node1Step3Chunk2_2_checked, root6Node1Step3Chunk2_3_checked, root6Node1Step3Chunk2_4_checked, root6Node1Step3Chunk2_5_checked, root6Node1Step3Chunk3_0_checked, root6Node1Step3Chunk3_1_checked, root6Node1Step3Chunk3_2_checked, root6Node1Step3Chunk3_3_checked, root6Node1Step3Chunk3_4_checked, root6Node1Step3Chunk3_5_checked, root6Node1Step3Chunk4_0_checked, root6Node1Step3Chunk4_1_checked, root6Node1Step3Chunk4_2_checked, root6Node1Step3Chunk4_3_checked, root6Node1Step3Chunk4_4_checked, root6Node1Step3Chunk4_5_checked, root6Node1Step3Chunk5_0_checked, root6Node1Step3Chunk5_1_checked, root6Node1Step3Chunk5_2_checked, root6Node1Step3Chunk5_3_checked, root6Node1Step3Chunk5_4_checked, root6Node1Step3Chunk5_5_checked, root6Node1Step3Chunk6_0_checked, root6Node1Step3Chunk6_1_checked, root6Node1Step3Chunk6_2_checked, root6Node1Step3Chunk6_3_checked, root6Node1Step3Chunk6_4_checked, root6Node1Step3Chunk6_5_checked, root6Node1Step3Chunk7_0_checked, root6Node1Step3Chunk7_1_checked, root6Node1Step3Chunk7_2_checked, root6Node1Step3Chunk7_3_checked, root6Node1Step3Chunk7_4_checked, root6Node1Step3Chunk7_5_checked, root6Node1Step3Chunk8_0_checked, root6Node1Step3Chunk8_1_checked, root6Node1Step3Chunk8_2_checked, root6Node1Step3Chunk8_3_checked, root6Node1Step3Chunk8_4_checked, root6Node1Step3Chunk8_5_checked, Bool.true_and])
theorem root6Node1Step3_checked :
    checkReplacement table57 root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq
    root6Node1Step3Narrowing_checked (by decide)
def root6Node1Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,2),(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2),(5,2),(8,2)]
  | 4 => [(5,0),(5,3)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4),(8,4)]
  | 11 => [(0,0),(1,3)]
  | 12 => [(7,2),(8,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(7,5)]
  | 16 => [(0,3)]
  | 17 => [(8,1)]
  | 18 => [(1,5),(6,5)]
  | 19 => [(0,4),(6,1)]
  | 20 => [(5,1),(5,4),(8,1)]
  | 21 => [(7,2)]
  | 22 => [(7,4)]
  | 23 => [(1,3)]
  | 24 => [(4,2)]
  | 25 => [(5,3)]
  | 26 => [(5,5)]
  | 27 => [(7,0)]
  | 28 => [(4,3),(8,3)]
  | 29 => [(1,5),(3,5),(5,5)]
  | 30 => [(1,1),(6,1)]
  | 31 => [(8,1)]
  | 32 => [(6,5)]
  | 33 => [(0,4)]
  | 34 => [(1,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(1,4)]
  | 38 => [(0,5)]
  | 39 => [(2,0),(2,4),(4,4)]
  | 40 => [(7,0),(8,0)]
  | 41 => [(8,3)]
  | 42 => [(5,5)]
  | 43 => [(3,0)]
  | 44 => [(2,5)]
  | 45 => [(6,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(6,0)]
  | 49 => [(3,1),(7,1)]
  | 50 => [(0,1),(1,5),(6,5),(7,5)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(8,2)]
  | 59 => [(5,0),(8,0)]
  | 60 => [(4,5),(7,3)]
  | 61 => [(6,0)]
  | 62 => [(7,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(8,4)]
  | 69 => [(0,0),(6,4)]
  | 70 => [(5,0)]
  | 71 => [(4,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(8,5)]
  | 75 => [(1,0)]
  | 76 => [(7,1)]
  | 77 => [(1,5),(7,5)]
  | 78 => [(0,0)]
  | 79 => [(7,2)]
  | 80 => [(7,4)]
  | 81 => [(1,3),(6,3)]
  | 82 => [(7,2),(8,2)]
  | 83 => [(4,0),(5,0),(8,0)]
  | 84 => [(4,5),(7,3)]
  | 85 => [(6,1)]
  | 86 => [(4,1),(8,1)]
  | 87 => [(0,2),(6,5)]
  | 88 => [(0,4),(1,1)]
  | 89 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,4)]
def root6Node1Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,2),(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2),(5,2),(8,2)]
  | 4 => some [(5,0),(5,3)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4),(8,4)]
  | 11 => some [(0,0),(1,3)]
  | 12 => some [(7,2),(8,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(7,5)]
  | 16 => some [(0,3)]
  | 17 => some [(8,1)]
  | 18 => some [(1,5),(6,5)]
  | 19 => some [(0,4),(6,1)]
  | 20 => some [(5,1),(5,4),(8,1)]
  | 21 => some [(7,2)]
  | 22 => some [(7,4)]
  | 23 => some [(1,3)]
  | 24 => some [(4,2)]
  | 25 => some [(5,3)]
  | 26 => some [(5,5)]
  | 27 => some [(7,0)]
  | 28 => some [(4,3),(8,3)]
  | 29 => some [(1,5),(3,5),(5,5)]
  | 30 => some [(1,1),(6,1)]
  | 31 => some [(8,1)]
  | 32 => some [(6,5)]
  | 33 => some [(0,4)]
  | 34 => some [(1,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(1,4)]
  | 38 => some [(0,5)]
  | 39 => some [(2,0),(2,4),(4,4)]
  | 40 => some [(7,0),(8,0)]
  | 41 => some [(8,3)]
  | 42 => some [(5,5)]
  | 43 => some [(3,0)]
  | 44 => some [(2,5)]
  | 45 => some [(6,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(6,0)]
  | 49 => some [(3,1),(7,1)]
  | 50 => some [(0,1),(1,5),(6,5),(7,5)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(8,2)]
  | 59 => some [(5,0),(8,0)]
  | 60 => some [(4,5),(7,3)]
  | 61 => some [(6,0)]
  | 62 => some [(7,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(8,4)]
  | 69 => some [(0,0),(6,4)]
  | 70 => some [(5,0)]
  | 71 => some [(4,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(7,1)]
  | 77 => some [(1,5),(7,5)]
  | 78 => some [(0,0)]
  | 79 => some [(7,2)]
  | 80 => some [(7,4)]
  | 81 => some [(1,3),(6,3)]
  | 82 => some [(7,2),(8,2)]
  | 83 => some [(4,0),(5,0),(8,0)]
  | 84 => some [(4,5),(7,3)]
  | 85 => some [(6,1)]
  | 86 => some [(4,1),(8,1)]
  | 87 => some [(0,2),(6,5)]
  | 88 => some [(0,4),(1,1)]
  | 89 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root6Node1Domains4_fast_eq : root6Node1Domains4 = expandDomains root6Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root6Node1Domains4 v = expandDomains root6Node1Domains4Fast v from by decide) v
theorem root6Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Narrowing_checked :
    checkNarrowing table6 root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_flatten table6Scope [table6Rows0_0,table6Rows0_1,table6Rows0_2,table6Rows0_3,table6Rows0_4,table6Rows0_5,table6Rows1_0,table6Rows1_1,table6Rows1_2,table6Rows1_3,table6Rows1_4,table6Rows1_5,table6Rows2_0,table6Rows2_1,table6Rows2_2,table6Rows2_3,table6Rows2_4,table6Rows2_5,table6Rows3_0,table6Rows3_1,table6Rows3_2,table6Rows3_3,table6Rows3_4,table6Rows3_5,table6Rows4_0,table6Rows4_1,table6Rows4_2,table6Rows4_3,table6Rows4_4,table6Rows4_5,table6Rows5_0,table6Rows5_1,table6Rows5_2,table6Rows5_3,table6Rows5_4,table6Rows5_5,table6Rows6_0,table6Rows6_1,table6Rows6_2,table6Rows6_3,table6Rows6_4,table6Rows6_5,table6Rows7_0,table6Rows7_1,table6Rows7_2,table6Rows7_3,table6Rows7_4,table6Rows7_5,table6Rows8_0,table6Rows8_1,table6Rows8_2,table6Rows8_3,table6Rows8_4,table6Rows8_5]
    root6Node1Domains3 root6Node1Domains4 (by
      simp only [List.all_cons, List.all_nil, root6Node1Step4Chunk0_0_checked, root6Node1Step4Chunk0_1_checked, root6Node1Step4Chunk0_2_checked, root6Node1Step4Chunk0_3_checked, root6Node1Step4Chunk0_4_checked, root6Node1Step4Chunk0_5_checked, root6Node1Step4Chunk1_0_checked, root6Node1Step4Chunk1_1_checked, root6Node1Step4Chunk1_2_checked, root6Node1Step4Chunk1_3_checked, root6Node1Step4Chunk1_4_checked, root6Node1Step4Chunk1_5_checked, root6Node1Step4Chunk2_0_checked, root6Node1Step4Chunk2_1_checked, root6Node1Step4Chunk2_2_checked, root6Node1Step4Chunk2_3_checked, root6Node1Step4Chunk2_4_checked, root6Node1Step4Chunk2_5_checked, root6Node1Step4Chunk3_0_checked, root6Node1Step4Chunk3_1_checked, root6Node1Step4Chunk3_2_checked, root6Node1Step4Chunk3_3_checked, root6Node1Step4Chunk3_4_checked, root6Node1Step4Chunk3_5_checked, root6Node1Step4Chunk4_0_checked, root6Node1Step4Chunk4_1_checked, root6Node1Step4Chunk4_2_checked, root6Node1Step4Chunk4_3_checked, root6Node1Step4Chunk4_4_checked, root6Node1Step4Chunk4_5_checked, root6Node1Step4Chunk5_0_checked, root6Node1Step4Chunk5_1_checked, root6Node1Step4Chunk5_2_checked, root6Node1Step4Chunk5_3_checked, root6Node1Step4Chunk5_4_checked, root6Node1Step4Chunk5_5_checked, root6Node1Step4Chunk6_0_checked, root6Node1Step4Chunk6_1_checked, root6Node1Step4Chunk6_2_checked, root6Node1Step4Chunk6_3_checked, root6Node1Step4Chunk6_4_checked, root6Node1Step4Chunk6_5_checked, root6Node1Step4Chunk7_0_checked, root6Node1Step4Chunk7_1_checked, root6Node1Step4Chunk7_2_checked, root6Node1Step4Chunk7_3_checked, root6Node1Step4Chunk7_4_checked, root6Node1Step4Chunk7_5_checked, root6Node1Step4Chunk8_0_checked, root6Node1Step4Chunk8_1_checked, root6Node1Step4Chunk8_2_checked, root6Node1Step4Chunk8_3_checked, root6Node1Step4Chunk8_4_checked, root6Node1Step4Chunk8_5_checked, Bool.true_and])
theorem root6Node1Step4_checked :
    checkReplacement table6 root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq
    root6Node1Step4Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
