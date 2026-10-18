module

public import SpectreFinite.RadiusFiveRoot5Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable34
public import SpectreFinite.RadiusFiveTable55
public import SpectreFinite.RadiusFiveTable57
public import SpectreFinite.RadiusFiveTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node1Domains0 : Domains 91 State := restrict root5Node0Domains4 43 (1,3)
def root5Node1Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(1,3),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,2),(8,4)]
  | 3 => some [(1,4),(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(0,5),(1,3),(4,5),(6,3),(7,3)]
  | 5 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(8,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 8 => some [(0,4),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 10 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 11 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 12 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => some [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3),(8,3)]
  | 14 => some [(1,2),(3,2),(5,2),(5,5),(7,2),(8,5)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(4,3),(7,3),(8,3)]
  | 17 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 18 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 19 => some [(2,1),(2,5),(4,1),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0),(7,0)]
  | 21 => some [(0,1),(1,4),(1,5),(3,4),(6,5),(7,4),(7,5)]
  | 22 => some [(0,3),(0,4),(0,5),(6,1),(6,2),(6,3)]
  | 23 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 24 => some [(0,1),(1,4),(7,4)]
  | 25 => some [(0,5),(6,2),(6,3)]
  | 26 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 27 => some [(0,0),(1,3),(3,3),(7,3)]
  | 28 => some [(3,2),(5,2),(7,2)]
  | 29 => some [(4,0),(7,4),(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,3),(7,5),(8,5)]
  | 31 => some [(0,2),(1,0),(4,2),(6,0),(7,0)]
  | 32 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 33 => some [(4,1),(7,5),(8,5)]
  | 34 => some [(0,2),(1,0),(6,0)]
  | 35 => some [(1,1),(3,1),(7,1)]
  | 36 => some [(0,1),(1,5),(6,5)]
  | 37 => some [(0,4),(6,1),(6,2)]
  | 38 => some [(5,1),(5,4),(8,1),(8,4)]
  | 39 => some [(0,1),(1,4),(6,4),(6,5)]
  | 40 => some [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 42 => some [(4,0),(7,4),(8,0)]
  | 43 => some [(1,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(1,0),(7,0)]
  | 48 => some [(4,3),(7,1),(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0),(7,0)]
  | 51 => some [(0,3),(0,4),(1,1),(6,1),(6,2)]
  | 52 => some [(5,1),(5,4),(8,1),(8,4)]
  | 53 => some [(0,1),(6,4),(6,5)]
  | 54 => some [(0,4),(1,2),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(4,0),(7,4)]
  | 59 => some [(1,3),(6,3),(7,3)]
  | 60 => some [(4,2),(7,2),(8,2)]
  | 61 => some [(4,3),(5,3),(7,1),(8,3)]
  | 62 => some [(5,5),(7,5),(8,5)]
  | 63 => some [(0,3),(1,0),(7,0)]
  | 64 => some [(4,3),(7,1),(8,1)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1),(5,1),(8,1)]
  | 68 => some [(0,1),(0,2),(6,5)]
  | 69 => some [(0,4),(1,1),(6,2)]
  | 70 => some [(0,5),(1,3),(7,3)]
  | 71 => some [(4,2),(4,4),(8,2)]
  | 72 => some [(1,4),(5,0),(5,3)]
  | 73 => some [(0,5),(4,5),(5,5),(8,5)]
  | 74 => some [(2,0),(7,0)]
  | 75 => some [(7,3),(8,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(1,0),(3,0),(7,0),(8,0)]
  | 78 => some [(0,4),(1,2),(6,2),(7,1)]
  | 79 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 80 => some [(0,0),(0,5),(6,0),(6,3)]
  | 81 => some [(3,1),(4,4),(7,2)]
  | 82 => some [(0,1),(1,4),(7,4)]
  | 83 => some [(0,5),(1,3),(6,2),(6,3)]
  | 84 => some [(4,4),(7,2),(8,2),(8,4)]
  | 85 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(7,3)]
  | 86 => some [(0,2),(1,5),(6,0),(8,2)]
  | 87 => some [(1,1),(5,0),(6,1),(7,1)]
  | 88 => some [(4,1),(4,5),(7,5),(8,1)]
  | 89 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node1Domains0_fast_eq : root5Node1Domains0 = expandDomains root5Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node1Domains0 v = expandDomains root5Node1Domains0Fast v from by decide) v
def root5Node1Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(7,4),(8,4)]
  | 1 => [(0,0),(0,5),(1,3),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,2),(8,4)]
  | 3 => [(1,4),(4,0),(5,0),(7,4),(8,0)]
  | 4 => [(0,5),(1,3),(4,5),(6,3),(7,3)]
  | 5 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => [(2,1),(2,3),(2,5),(4,1),(4,5),(8,1)]
  | 7 => [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 8 => [(0,4),(1,1),(6,1),(7,1)]
  | 9 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 10 => [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 11 => [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 12 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3),(8,3)]
  | 14 => [(1,2),(3,2),(5,2),(7,2)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5),(8,2)]
  | 18 => [(1,0),(3,0),(5,0)]
  | 19 => [(2,1),(2,5),(4,1),(4,5)]
  | 20 => [(0,2),(1,0),(6,0),(7,0)]
  | 21 => [(0,1),(1,4),(1,5),(3,4),(6,5),(7,4),(7,5)]
  | 22 => [(0,3),(0,4),(6,1)]
  | 23 => [(5,1),(5,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(5,2),(7,2)]
  | 29 => [(4,0),(7,4),(8,0)]
  | 30 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,3),(7,5),(8,5)]
  | 31 => [(4,2),(7,0)]
  | 32 => [(4,3),(5,3),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1),(5,4),(8,1),(8,4)]
  | 39 => [(0,1),(1,4),(6,4),(6,5)]
  | 40 => [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(7,5),(8,5)]
  | 50 => [(0,3),(1,0),(6,0),(7,0)]
  | 51 => [(0,3),(1,1),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(4,2),(7,2),(8,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(0,4),(1,1),(6,2)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(1,0),(3,0),(7,0),(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(4,4),(7,2),(8,2),(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node1Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(1,3),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,2),(8,4)]
  | 3 => some [(1,4),(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(0,5),(1,3),(4,5),(6,3),(7,3)]
  | 5 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(8,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(6,5)]
  | 8 => some [(0,4),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 10 => some [(0,0),(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 11 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 12 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => some [(0,0),(1,3),(3,3),(5,3),(6,4),(7,3),(8,3)]
  | 14 => some [(1,2),(3,2),(5,2),(7,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,1),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0),(7,0)]
  | 21 => some [(0,1),(1,4),(1,5),(3,4),(6,5),(7,4),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(5,2),(7,2)]
  | 29 => some [(4,0),(7,4),(8,0)]
  | 30 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,3),(7,5),(8,5)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1),(5,4),(8,1),(8,4)]
  | 39 => some [(0,1),(1,4),(6,4),(6,5)]
  | 40 => some [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(4,2),(7,2),(8,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(0,4),(1,1),(6,2)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(1,0),(3,0),(7,0),(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(4,4),(7,2),(8,2),(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node1Domains1_fast_eq : root5Node1Domains1 = expandDomains root5Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node1Domains1 v = expandDomains root5Node1Domains1Fast v from by decide) v
theorem root5Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq (by decide)
theorem root5Node1Step1Narrowing_checked :
    checkNarrowing table55 root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root5Node1Domains0 root5Node1Domains1 (by
      simp only [List.all_cons, List.all_nil, root5Node1Step1Chunk0_0_checked, root5Node1Step1Chunk0_1_checked, root5Node1Step1Chunk0_2_checked, root5Node1Step1Chunk0_3_checked, root5Node1Step1Chunk0_4_checked, root5Node1Step1Chunk0_5_checked, root5Node1Step1Chunk1_0_checked, root5Node1Step1Chunk1_1_checked, root5Node1Step1Chunk1_2_checked, root5Node1Step1Chunk1_3_checked, root5Node1Step1Chunk1_4_checked, root5Node1Step1Chunk1_5_checked, root5Node1Step1Chunk2_0_checked, root5Node1Step1Chunk2_1_checked, root5Node1Step1Chunk2_2_checked, root5Node1Step1Chunk2_3_checked, root5Node1Step1Chunk2_4_checked, root5Node1Step1Chunk2_5_checked, root5Node1Step1Chunk3_0_checked, root5Node1Step1Chunk3_1_checked, root5Node1Step1Chunk3_2_checked, root5Node1Step1Chunk3_3_checked, root5Node1Step1Chunk3_4_checked, root5Node1Step1Chunk3_5_checked, root5Node1Step1Chunk4_0_checked, root5Node1Step1Chunk4_1_checked, root5Node1Step1Chunk4_2_checked, root5Node1Step1Chunk4_3_checked, root5Node1Step1Chunk4_4_checked, root5Node1Step1Chunk4_5_checked, root5Node1Step1Chunk5_0_checked, root5Node1Step1Chunk5_1_checked, root5Node1Step1Chunk5_2_checked, root5Node1Step1Chunk5_3_checked, root5Node1Step1Chunk5_4_checked, root5Node1Step1Chunk5_5_checked, root5Node1Step1Chunk6_0_checked, root5Node1Step1Chunk6_1_checked, root5Node1Step1Chunk6_2_checked, root5Node1Step1Chunk6_3_checked, root5Node1Step1Chunk6_4_checked, root5Node1Step1Chunk6_5_checked, root5Node1Step1Chunk7_0_checked, root5Node1Step1Chunk7_1_checked, root5Node1Step1Chunk7_2_checked, root5Node1Step1Chunk7_3_checked, root5Node1Step1Chunk7_4_checked, root5Node1Step1Chunk7_5_checked, root5Node1Step1Chunk8_0_checked, root5Node1Step1Chunk8_1_checked, root5Node1Step1Chunk8_2_checked, root5Node1Step1Chunk8_3_checked, root5Node1Step1Chunk8_4_checked, root5Node1Step1Chunk8_5_checked, Bool.true_and])
theorem root5Node1Step1_checked :
    checkReplacement table55 root5Node1Domains0 root5Node1Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root5Node1Domains0 root5Node1Domains1
    root5Node1Domains0Fast root5Node1Domains1Fast
    root5Node1Domains0_fast_eq root5Node1Domains1_fast_eq
    root5Node1Step1Narrowing_checked (by decide)
def root5Node1Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(4,0),(7,4)]
  | 4 => [(0,5),(1,3),(6,3),(7,3)]
  | 5 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 7 => [(0,2),(1,0),(6,0)]
  | 8 => [(1,1),(7,1)]
  | 9 => [(4,1),(5,1),(7,5),(8,1)]
  | 10 => [(0,1),(0,2),(6,0),(6,5)]
  | 11 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 12 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => [(0,0),(1,3),(6,4)]
  | 14 => [(1,2),(3,2),(5,2),(7,2)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5),(8,2)]
  | 18 => [(1,0),(3,0),(5,0)]
  | 19 => [(2,1),(2,5),(4,5)]
  | 20 => [(0,2),(1,0),(6,0),(7,0)]
  | 21 => [(1,5),(6,5),(7,5)]
  | 22 => [(0,3),(0,4),(6,1)]
  | 23 => [(5,1),(5,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(7,2)]
  | 29 => [(4,0),(7,4),(8,0)]
  | 30 => [(4,5),(7,3),(8,5)]
  | 31 => [(4,2),(7,0)]
  | 32 => [(4,3),(5,3),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1),(8,1)]
  | 39 => [(0,1),(1,4),(6,4),(6,5)]
  | 40 => [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(7,5),(8,5)]
  | 50 => [(0,3),(1,0),(6,0),(7,0)]
  | 51 => [(0,3),(1,1),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(4,2),(7,2),(8,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(0,4),(1,1),(6,2)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(1,0),(3,0),(7,0),(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(4,4),(7,2),(8,2),(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(0,4),(1,1),(7,1)]
def root5Node1Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(7,4)]
  | 1 => some [(0,5),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(4,0),(7,4)]
  | 4 => some [(0,5),(1,3),(6,3),(7,3)]
  | 5 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 7 => some [(0,2),(1,0),(6,0)]
  | 8 => some [(1,1),(7,1)]
  | 9 => some [(4,1),(5,1),(7,5),(8,1)]
  | 10 => some [(0,1),(0,2),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 12 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => some [(0,0),(1,3),(6,4)]
  | 14 => some [(1,2),(3,2),(5,2),(7,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0),(7,0)]
  | 21 => some [(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0),(7,4),(8,0)]
  | 30 => some [(4,5),(7,3),(8,5)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1),(8,1)]
  | 39 => some [(0,1),(1,4),(6,4),(6,5)]
  | 40 => some [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(7,5),(8,5)]
  | 50 => some [(0,3),(1,0),(6,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(4,2),(7,2),(8,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(0,4),(1,1),(6,2)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(1,0),(3,0),(7,0),(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(4,4),(7,2),(8,2),(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root5Node1Domains2_fast_eq : root5Node1Domains2 = expandDomains root5Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node1Domains2 v = expandDomains root5Node1Domains2Fast v from by decide) v
theorem root5Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_0⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_1⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_2⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_3⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_4⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_5⟩
      root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq (by decide)
theorem root5Node1Step2Narrowing_checked :
    checkNarrowing table34 root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkNarrowing_flatten table34Scope [table34Rows0_0,table34Rows0_1,table34Rows0_2,table34Rows0_3,table34Rows0_4,table34Rows0_5,table34Rows1_0,table34Rows1_1,table34Rows1_2,table34Rows1_3,table34Rows1_4,table34Rows1_5,table34Rows2_0,table34Rows2_1,table34Rows2_2,table34Rows2_3,table34Rows2_4,table34Rows2_5,table34Rows3_0,table34Rows3_1,table34Rows3_2,table34Rows3_3,table34Rows3_4,table34Rows3_5,table34Rows4_0,table34Rows4_1,table34Rows4_2,table34Rows4_3,table34Rows4_4,table34Rows4_5,table34Rows5_0,table34Rows5_1,table34Rows5_2,table34Rows5_3,table34Rows5_4,table34Rows5_5,table34Rows6_0,table34Rows6_1,table34Rows6_2,table34Rows6_3,table34Rows6_4,table34Rows6_5,table34Rows7_0,table34Rows7_1,table34Rows7_2,table34Rows7_3,table34Rows7_4,table34Rows7_5,table34Rows8_0,table34Rows8_1,table34Rows8_2,table34Rows8_3,table34Rows8_4,table34Rows8_5]
    root5Node1Domains1 root5Node1Domains2 (by
      simp only [List.all_cons, List.all_nil, root5Node1Step2Chunk0_0_checked, root5Node1Step2Chunk0_1_checked, root5Node1Step2Chunk0_2_checked, root5Node1Step2Chunk0_3_checked, root5Node1Step2Chunk0_4_checked, root5Node1Step2Chunk0_5_checked, root5Node1Step2Chunk1_0_checked, root5Node1Step2Chunk1_1_checked, root5Node1Step2Chunk1_2_checked, root5Node1Step2Chunk1_3_checked, root5Node1Step2Chunk1_4_checked, root5Node1Step2Chunk1_5_checked, root5Node1Step2Chunk2_0_checked, root5Node1Step2Chunk2_1_checked, root5Node1Step2Chunk2_2_checked, root5Node1Step2Chunk2_3_checked, root5Node1Step2Chunk2_4_checked, root5Node1Step2Chunk2_5_checked, root5Node1Step2Chunk3_0_checked, root5Node1Step2Chunk3_1_checked, root5Node1Step2Chunk3_2_checked, root5Node1Step2Chunk3_3_checked, root5Node1Step2Chunk3_4_checked, root5Node1Step2Chunk3_5_checked, root5Node1Step2Chunk4_0_checked, root5Node1Step2Chunk4_1_checked, root5Node1Step2Chunk4_2_checked, root5Node1Step2Chunk4_3_checked, root5Node1Step2Chunk4_4_checked, root5Node1Step2Chunk4_5_checked, root5Node1Step2Chunk5_0_checked, root5Node1Step2Chunk5_1_checked, root5Node1Step2Chunk5_2_checked, root5Node1Step2Chunk5_3_checked, root5Node1Step2Chunk5_4_checked, root5Node1Step2Chunk5_5_checked, root5Node1Step2Chunk6_0_checked, root5Node1Step2Chunk6_1_checked, root5Node1Step2Chunk6_2_checked, root5Node1Step2Chunk6_3_checked, root5Node1Step2Chunk6_4_checked, root5Node1Step2Chunk6_5_checked, root5Node1Step2Chunk7_0_checked, root5Node1Step2Chunk7_1_checked, root5Node1Step2Chunk7_2_checked, root5Node1Step2Chunk7_3_checked, root5Node1Step2Chunk7_4_checked, root5Node1Step2Chunk7_5_checked, root5Node1Step2Chunk8_0_checked, root5Node1Step2Chunk8_1_checked, root5Node1Step2Chunk8_2_checked, root5Node1Step2Chunk8_3_checked, root5Node1Step2Chunk8_4_checked, root5Node1Step2Chunk8_5_checked, Bool.true_and])
theorem root5Node1Step2_checked :
    checkReplacement table34 root5Node1Domains1 root5Node1Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root5Node1Domains1 root5Node1Domains2
    root5Node1Domains1Fast root5Node1Domains2Fast
    root5Node1Domains1_fast_eq root5Node1Domains2_fast_eq
    root5Node1Step2Narrowing_checked (by decide)
def root5Node1Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(4,0),(7,4)]
  | 4 => [(0,5),(1,3),(6,3),(7,3)]
  | 5 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 7 => [(0,2),(1,0),(6,0)]
  | 8 => [(1,1),(7,1)]
  | 9 => [(4,1),(5,1),(7,5),(8,1)]
  | 10 => [(0,1),(0,2),(6,0),(6,5)]
  | 11 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 12 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => [(0,0),(1,3),(6,4)]
  | 14 => [(1,2),(3,2),(5,2),(7,2)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5),(8,2)]
  | 18 => [(1,0),(3,0),(5,0)]
  | 19 => [(2,1),(2,5),(4,5)]
  | 20 => [(0,2),(1,0),(6,0),(7,0)]
  | 21 => [(1,5),(6,5),(7,5)]
  | 22 => [(0,3),(0,4),(6,1)]
  | 23 => [(5,1),(5,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(7,2)]
  | 29 => [(4,0),(7,4)]
  | 30 => [(4,5),(7,3),(8,5)]
  | 31 => [(4,2),(7,0)]
  | 32 => [(4,3),(5,3),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1),(8,1)]
  | 39 => [(0,1),(6,5)]
  | 40 => [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(0,3),(1,1),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node1Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(7,4)]
  | 1 => some [(0,5),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(4,0),(7,4)]
  | 4 => some [(0,5),(1,3),(6,3),(7,3)]
  | 5 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 7 => some [(0,2),(1,0),(6,0)]
  | 8 => some [(1,1),(7,1)]
  | 9 => some [(4,1),(5,1),(7,5),(8,1)]
  | 10 => some [(0,1),(0,2),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 12 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => some [(0,0),(1,3),(6,4)]
  | 14 => some [(1,2),(3,2),(5,2),(7,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0),(7,0)]
  | 21 => some [(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0),(7,4)]
  | 30 => some [(4,5),(7,3),(8,5)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1),(8,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0),(1,3),(3,3),(6,3),(6,4),(7,3)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node1Domains3_fast_eq : root5Node1Domains3 = expandDomains root5Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node1Domains3 v = expandDomains root5Node1Domains3Fast v from by decide) v
theorem root5Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq (by decide)
theorem root5Node1Step3Narrowing_checked :
    checkNarrowing table57 root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root5Node1Domains2 root5Node1Domains3 (by
      simp only [List.all_cons, List.all_nil, root5Node1Step3Chunk0_0_checked, root5Node1Step3Chunk0_1_checked, root5Node1Step3Chunk0_2_checked, root5Node1Step3Chunk0_3_checked, root5Node1Step3Chunk0_4_checked, root5Node1Step3Chunk0_5_checked, root5Node1Step3Chunk1_0_checked, root5Node1Step3Chunk1_1_checked, root5Node1Step3Chunk1_2_checked, root5Node1Step3Chunk1_3_checked, root5Node1Step3Chunk1_4_checked, root5Node1Step3Chunk1_5_checked, root5Node1Step3Chunk2_0_checked, root5Node1Step3Chunk2_1_checked, root5Node1Step3Chunk2_2_checked, root5Node1Step3Chunk2_3_checked, root5Node1Step3Chunk2_4_checked, root5Node1Step3Chunk2_5_checked, root5Node1Step3Chunk3_0_checked, root5Node1Step3Chunk3_1_checked, root5Node1Step3Chunk3_2_checked, root5Node1Step3Chunk3_3_checked, root5Node1Step3Chunk3_4_checked, root5Node1Step3Chunk3_5_checked, root5Node1Step3Chunk4_0_checked, root5Node1Step3Chunk4_1_checked, root5Node1Step3Chunk4_2_checked, root5Node1Step3Chunk4_3_checked, root5Node1Step3Chunk4_4_checked, root5Node1Step3Chunk4_5_checked, root5Node1Step3Chunk5_0_checked, root5Node1Step3Chunk5_1_checked, root5Node1Step3Chunk5_2_checked, root5Node1Step3Chunk5_3_checked, root5Node1Step3Chunk5_4_checked, root5Node1Step3Chunk5_5_checked, root5Node1Step3Chunk6_0_checked, root5Node1Step3Chunk6_1_checked, root5Node1Step3Chunk6_2_checked, root5Node1Step3Chunk6_3_checked, root5Node1Step3Chunk6_4_checked, root5Node1Step3Chunk6_5_checked, root5Node1Step3Chunk7_0_checked, root5Node1Step3Chunk7_1_checked, root5Node1Step3Chunk7_2_checked, root5Node1Step3Chunk7_3_checked, root5Node1Step3Chunk7_4_checked, root5Node1Step3Chunk7_5_checked, root5Node1Step3Chunk8_0_checked, root5Node1Step3Chunk8_1_checked, root5Node1Step3Chunk8_2_checked, root5Node1Step3Chunk8_3_checked, root5Node1Step3Chunk8_4_checked, root5Node1Step3Chunk8_5_checked, Bool.true_and])
theorem root5Node1Step3_checked :
    checkReplacement table57 root5Node1Domains2 root5Node1Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root5Node1Domains2 root5Node1Domains3
    root5Node1Domains2Fast root5Node1Domains3Fast
    root5Node1Domains2_fast_eq root5Node1Domains3_fast_eq
    root5Node1Step3Narrowing_checked (by decide)
def root5Node1Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(7,4)]
  | 1 => [(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(4,0),(7,4)]
  | 4 => [(0,5),(1,3),(6,3),(7,3)]
  | 5 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 7 => [(0,2),(1,0),(6,0)]
  | 8 => [(1,1),(7,1)]
  | 9 => [(4,1),(5,1),(7,5),(8,1)]
  | 10 => [(0,1),(0,2),(6,0),(6,5)]
  | 11 => [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 12 => [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => [(0,0),(1,3),(6,4)]
  | 14 => [(1,2),(3,2),(5,2),(7,2)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5),(8,2)]
  | 18 => [(1,0),(3,0),(5,0)]
  | 19 => [(2,1),(2,5),(4,5)]
  | 20 => [(0,2),(1,0),(6,0),(7,0)]
  | 21 => [(1,5),(6,5),(7,5)]
  | 22 => [(0,3),(0,4),(6,1)]
  | 23 => [(5,1),(5,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(0,0)]
  | 28 => [(3,2),(7,2)]
  | 29 => [(4,0),(7,4)]
  | 30 => [(4,5),(7,3),(8,5)]
  | 31 => [(4,2),(7,0)]
  | 32 => [(4,3),(5,3),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1),(8,1)]
  | 39 => [(0,1),(6,5)]
  | 40 => [(0,0),(6,3),(6,4)]
  | 41 => [(1,2),(7,2)]
  | 42 => [(7,4)]
  | 43 => [(1,3)]
  | 44 => [(8,2)]
  | 45 => [(5,0)]
  | 46 => [(4,5)]
  | 47 => [(7,0)]
  | 48 => [(8,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(0,3),(1,1),(6,1)]
  | 52 => [(8,1)]
  | 53 => [(6,5)]
  | 54 => [(0,4)]
  | 55 => [(5,4)]
  | 56 => [(0,0)]
  | 57 => [(7,2)]
  | 58 => [(7,4)]
  | 59 => [(6,3)]
  | 60 => [(7,2)]
  | 61 => [(5,3),(8,3)]
  | 62 => [(5,5)]
  | 63 => [(7,0)]
  | 64 => [(4,3)]
  | 65 => [(1,5)]
  | 66 => [(6,1)]
  | 67 => [(4,1)]
  | 68 => [(0,2)]
  | 69 => [(1,1)]
  | 70 => [(0,5)]
  | 71 => [(4,4)]
  | 72 => [(1,4)]
  | 73 => [(0,5)]
  | 74 => [(2,0)]
  | 75 => [(7,3)]
  | 76 => [(5,2)]
  | 77 => [(8,0)]
  | 78 => [(7,1)]
  | 79 => [(7,5)]
  | 80 => [(6,0)]
  | 81 => [(3,1)]
  | 82 => [(0,1)]
  | 83 => [(6,2)]
  | 84 => [(8,4)]
  | 85 => [(7,3)]
  | 86 => [(8,2)]
  | 87 => [(5,0)]
  | 88 => [(4,5)]
  | 89 => [(1,0)]
  | _ => [(7,1)]
def root5Node1Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(7,4)]
  | 1 => some [(0,5),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(4,0),(7,4)]
  | 4 => some [(0,5),(1,3),(6,3),(7,3)]
  | 5 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,0)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 7 => some [(0,2),(1,0),(6,0)]
  | 8 => some [(1,1),(7,1)]
  | 9 => some [(4,1),(5,1),(7,5),(8,1)]
  | 10 => some [(0,1),(0,2),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(3,1),(6,2),(7,1)]
  | 12 => some [(0,1),(1,4),(1,5),(6,5),(7,4)]
  | 13 => some [(0,0),(1,3),(6,4)]
  | 14 => some [(1,2),(3,2),(5,2),(7,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2)]
  | 18 => some [(1,0),(3,0),(5,0)]
  | 19 => some [(2,1),(2,5),(4,5)]
  | 20 => some [(0,2),(1,0),(6,0),(7,0)]
  | 21 => some [(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1)]
  | 23 => some [(5,1),(5,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(0,0)]
  | 28 => some [(3,2),(7,2)]
  | 29 => some [(4,0),(7,4)]
  | 30 => some [(4,5),(7,3),(8,5)]
  | 31 => some [(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1),(8,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0),(6,3),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(7,4)]
  | 43 => some [(1,3)]
  | 44 => some [(8,2)]
  | 45 => some [(5,0)]
  | 46 => some [(4,5)]
  | 47 => some [(7,0)]
  | 48 => some [(8,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3),(1,1),(6,1)]
  | 52 => some [(8,1)]
  | 53 => some [(6,5)]
  | 54 => some [(0,4)]
  | 55 => some [(5,4)]
  | 56 => some [(0,0)]
  | 57 => some [(7,2)]
  | 58 => some [(7,4)]
  | 59 => some [(6,3)]
  | 60 => some [(7,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5)]
  | 63 => some [(7,0)]
  | 64 => some [(4,3)]
  | 65 => some [(1,5)]
  | 66 => some [(6,1)]
  | 67 => some [(4,1)]
  | 68 => some [(0,2)]
  | 69 => some [(1,1)]
  | 70 => some [(0,5)]
  | 71 => some [(4,4)]
  | 72 => some [(1,4)]
  | 73 => some [(0,5)]
  | 74 => some [(2,0)]
  | 75 => some [(7,3)]
  | 76 => some [(5,2)]
  | 77 => some [(8,0)]
  | 78 => some [(7,1)]
  | 79 => some [(7,5)]
  | 80 => some [(6,0)]
  | 81 => some [(3,1)]
  | 82 => some [(0,1)]
  | 83 => some [(6,2)]
  | 84 => some [(8,4)]
  | 85 => some [(7,3)]
  | 86 => some [(8,2)]
  | 87 => some [(5,0)]
  | 88 => some [(4,5)]
  | 89 => some [(1,0)]
  | _ => some [(7,1)]
theorem root5Node1Domains4_fast_eq : root5Node1Domains4 = expandDomains root5Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root5Node1Domains4 v = expandDomains root5Node1Domains4Fast v from by decide) v
theorem root5Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq (by decide)
theorem root5Node1Step4Narrowing_checked :
    checkNarrowing table6 root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkNarrowing_flatten table6Scope [table6Rows0_0,table6Rows0_1,table6Rows0_2,table6Rows0_3,table6Rows0_4,table6Rows0_5,table6Rows1_0,table6Rows1_1,table6Rows1_2,table6Rows1_3,table6Rows1_4,table6Rows1_5,table6Rows2_0,table6Rows2_1,table6Rows2_2,table6Rows2_3,table6Rows2_4,table6Rows2_5,table6Rows3_0,table6Rows3_1,table6Rows3_2,table6Rows3_3,table6Rows3_4,table6Rows3_5,table6Rows4_0,table6Rows4_1,table6Rows4_2,table6Rows4_3,table6Rows4_4,table6Rows4_5,table6Rows5_0,table6Rows5_1,table6Rows5_2,table6Rows5_3,table6Rows5_4,table6Rows5_5,table6Rows6_0,table6Rows6_1,table6Rows6_2,table6Rows6_3,table6Rows6_4,table6Rows6_5,table6Rows7_0,table6Rows7_1,table6Rows7_2,table6Rows7_3,table6Rows7_4,table6Rows7_5,table6Rows8_0,table6Rows8_1,table6Rows8_2,table6Rows8_3,table6Rows8_4,table6Rows8_5]
    root5Node1Domains3 root5Node1Domains4 (by
      simp only [List.all_cons, List.all_nil, root5Node1Step4Chunk0_0_checked, root5Node1Step4Chunk0_1_checked, root5Node1Step4Chunk0_2_checked, root5Node1Step4Chunk0_3_checked, root5Node1Step4Chunk0_4_checked, root5Node1Step4Chunk0_5_checked, root5Node1Step4Chunk1_0_checked, root5Node1Step4Chunk1_1_checked, root5Node1Step4Chunk1_2_checked, root5Node1Step4Chunk1_3_checked, root5Node1Step4Chunk1_4_checked, root5Node1Step4Chunk1_5_checked, root5Node1Step4Chunk2_0_checked, root5Node1Step4Chunk2_1_checked, root5Node1Step4Chunk2_2_checked, root5Node1Step4Chunk2_3_checked, root5Node1Step4Chunk2_4_checked, root5Node1Step4Chunk2_5_checked, root5Node1Step4Chunk3_0_checked, root5Node1Step4Chunk3_1_checked, root5Node1Step4Chunk3_2_checked, root5Node1Step4Chunk3_3_checked, root5Node1Step4Chunk3_4_checked, root5Node1Step4Chunk3_5_checked, root5Node1Step4Chunk4_0_checked, root5Node1Step4Chunk4_1_checked, root5Node1Step4Chunk4_2_checked, root5Node1Step4Chunk4_3_checked, root5Node1Step4Chunk4_4_checked, root5Node1Step4Chunk4_5_checked, root5Node1Step4Chunk5_0_checked, root5Node1Step4Chunk5_1_checked, root5Node1Step4Chunk5_2_checked, root5Node1Step4Chunk5_3_checked, root5Node1Step4Chunk5_4_checked, root5Node1Step4Chunk5_5_checked, root5Node1Step4Chunk6_0_checked, root5Node1Step4Chunk6_1_checked, root5Node1Step4Chunk6_2_checked, root5Node1Step4Chunk6_3_checked, root5Node1Step4Chunk6_4_checked, root5Node1Step4Chunk6_5_checked, root5Node1Step4Chunk7_0_checked, root5Node1Step4Chunk7_1_checked, root5Node1Step4Chunk7_2_checked, root5Node1Step4Chunk7_3_checked, root5Node1Step4Chunk7_4_checked, root5Node1Step4Chunk7_5_checked, root5Node1Step4Chunk8_0_checked, root5Node1Step4Chunk8_1_checked, root5Node1Step4Chunk8_2_checked, root5Node1Step4Chunk8_3_checked, root5Node1Step4Chunk8_4_checked, root5Node1Step4Chunk8_5_checked, Bool.true_and])
theorem root5Node1Step4_checked :
    checkReplacement table6 root5Node1Domains3 root5Node1Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root5Node1Domains3 root5Node1Domains4
    root5Node1Domains3Fast root5Node1Domains4Fast
    root5Node1Domains3_fast_eq root5Node1Domains4_fast_eq
    root5Node1Step4Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
