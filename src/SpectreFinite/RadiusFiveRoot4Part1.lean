module

public import SpectreFinite.RadiusFiveRoot4Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable1
public import SpectreFinite.RadiusFiveTable33
public import SpectreFinite.RadiusFiveTable46
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node1Domains0 : Domains 91 State := restrict root4Node0Domains4 18 (7,0)
def root4Node1Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => some [(1,2),(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(7,4),(8,4)]
  | 4 => some [(0,0),(0,5),(1,3),(6,3)]
  | 5 => some [(4,4),(7,2),(8,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(7,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => some [(0,3),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5),(8,1)]
  | 10 => some [(0,2),(1,5),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(6,1),(7,1)]
  | 12 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => some [(0,0),(1,4),(4,0),(6,4),(7,4)]
  | 14 => some [(0,5),(1,2),(1,3),(3,2),(6,3),(7,2),(7,3)]
  | 15 => some [(2,0),(2,2),(4,0),(4,2)]
  | 16 => some [(3,3),(5,3),(7,3)]
  | 17 => some [(5,2),(5,5),(8,2),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3),(7,3),(8,3)]
  | 20 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 21 => some [(1,5),(4,1),(5,1),(7,5),(8,1)]
  | 22 => some [(0,1),(0,2),(0,3),(6,0),(6,1),(6,5)]
  | 23 => some [(0,4),(1,1),(3,1),(5,1),(6,2)]
  | 24 => some [(0,1),(1,4),(3,4),(7,4)]
  | 25 => some [(0,5),(6,2),(6,3)]
  | 26 => some [(4,4),(7,2),(8,4)]
  | 27 => some [(1,4),(6,4),(7,4)]
  | 28 => some [(0,5),(1,2),(6,3)]
  | 29 => some [(2,0),(2,2),(2,4),(4,4),(7,2),(7,4),(8,4)]
  | 30 => some [(4,5),(7,3),(8,3),(8,5)]
  | 31 => some [(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 32 => some [(1,0),(3,0),(5,0),(5,3),(7,0),(8,3)]
  | 33 => some [(2,1),(2,3),(2,5),(4,5),(8,5)]
  | 34 => some [(0,2),(1,0),(6,0)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(4,1),(7,5)]
  | 37 => some [(0,2),(0,3),(6,0)]
  | 38 => some [(1,1),(3,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => some [(0,0),(0,1),(1,4),(6,3),(6,4)]
  | 41 => some [(0,5),(1,2),(6,2),(7,2)]
  | 42 => some [(4,4),(7,4),(8,4)]
  | 43 => some [(0,0),(6,3),(6,4)]
  | 44 => some [(1,2),(3,2),(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(5,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,3),(8,5)]
  | 50 => some [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => some [(0,3),(1,0),(1,1),(6,0),(6,1)]
  | 52 => some [(4,1),(7,1),(8,1)]
  | 53 => some [(0,2),(1,5),(7,5)]
  | 54 => some [(0,3),(1,1),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,3),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 62 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 63 => some [(4,2),(7,0),(8,0)]
  | 64 => some [(5,3),(8,3)]
  | 65 => some [(5,5),(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,0),(6,1)]
  | 70 => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 71 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 72 => some [(1,4),(7,4)]
  | 73 => some [(0,5),(1,3),(6,3)]
  | 74 => some [(4,4),(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0),(8,2)]
  | 78 => some [(0,3),(1,1),(4,3),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(1,5),(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,1),(6,4)]
  | 84 => some [(1,2),(5,1),(6,2),(7,2)]
  | 85 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2),(8,5)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node1Domains0_fast_eq : root4Node1Domains0 = expandDomains root4Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node1Domains0 v = expandDomains root4Node1Domains0Fast v from by decide) v
def root4Node1Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4),(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4),(8,4)]
  | 4 => [(0,0),(0,5),(1,3),(6,3)]
  | 5 => [(4,4),(7,2),(8,2)]
  | 6 => [(4,3),(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5),(6,5)]
  | 11 => [(0,4),(1,1),(6,1),(7,1)]
  | 12 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => [(4,0),(7,4)]
  | 14 => [(1,3),(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3),(7,3),(8,3)]
  | 20 => [(1,5),(3,5),(4,2),(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 21 => [(5,1),(8,1)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(1,4),(3,4),(7,4)]
  | 25 => [(0,5),(6,3)]
  | 26 => [(4,4),(7,2)]
  | 27 => [(1,4),(7,4)]
  | 28 => [(0,5),(1,2),(6,3)]
  | 29 => [(2,0),(2,2),(2,4),(4,4),(7,2),(7,4),(8,4)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(1,0),(3,0),(7,0)]
  | 33 => [(2,1),(2,3),(2,5)]
  | 34 => [(0,2),(6,0)]
  | 35 => [(1,1),(7,1)]
  | 36 => [(4,1),(7,5)]
  | 37 => [(0,2),(6,0)]
  | 38 => [(1,1),(3,1),(7,1),(8,1)]
  | 39 => [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0),(6,4)]
  | 44 => [(1,2),(3,2),(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2),(8,2)]
  | 48 => [(5,0),(5,3),(8,0)]
  | 49 => [(4,5),(7,3),(8,3),(8,5)]
  | 50 => [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(1,4),(6,3),(6,4)]
  | 60 => [(0,5),(1,2),(7,2)]
  | 61 => [(5,0),(8,0)]
  | 62 => [(4,5),(7,3)]
  | 63 => [(4,2),(7,0)]
  | 64 => [(5,3),(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(2,1),(7,1)]
  | 68 => [(0,2),(1,5),(7,5)]
  | 69 => [(0,3),(1,1),(6,0),(6,1)]
  | 70 => [(0,0),(6,4)]
  | 71 => [(1,2),(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3),(6,3)]
  | 74 => [(7,2),(8,2)]
  | 75 => [(0,0),(4,0),(5,0),(8,0)]
  | 76 => [(3,2),(4,5),(7,3)]
  | 77 => [(4,0),(4,2),(7,0),(8,2)]
  | 78 => [(0,3),(1,1),(4,3),(6,1),(7,1)]
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(0,2),(6,0),(6,5)]
  | 81 => [(0,4),(1,1),(7,1)]
  | 82 => [(1,5),(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,1),(6,4)]
  | 84 => [(1,2),(5,1),(6,2),(7,2)]
  | 85 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,2),(8,5)]
  | 87 => [(5,0),(7,0),(8,0)]
  | 88 => [(4,3),(4,5),(8,3)]
  | 89 => [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root4Node1Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4),(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4),(8,4)]
  | 4 => some [(0,0),(0,5),(1,3),(6,3)]
  | 5 => some [(4,4),(7,2),(8,2)]
  | 6 => some [(4,3),(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5),(6,5)]
  | 11 => some [(0,4),(1,1),(6,1),(7,1)]
  | 12 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => some [(4,0),(7,4)]
  | 14 => some [(1,3),(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3),(7,3),(8,3)]
  | 20 => some [(1,5),(3,5),(4,2),(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 21 => some [(5,1),(8,1)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(1,4),(3,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(4,4),(7,2)]
  | 27 => some [(1,4),(7,4)]
  | 28 => some [(0,5),(1,2),(6,3)]
  | 29 => some [(2,0),(2,2),(2,4),(4,4),(7,2),(7,4),(8,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(1,0),(3,0),(7,0)]
  | 33 => some [(2,1),(2,3),(2,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(4,1),(7,5)]
  | 37 => some [(0,2),(6,0)]
  | 38 => some [(1,1),(3,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0),(6,4)]
  | 44 => some [(1,2),(3,2),(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2),(8,2)]
  | 48 => some [(5,0),(5,3),(8,0)]
  | 49 => some [(4,5),(7,3),(8,3),(8,5)]
  | 50 => some [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,3),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(5,0),(8,0)]
  | 62 => some [(4,5),(7,3)]
  | 63 => some [(4,2),(7,0)]
  | 64 => some [(5,3),(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(2,1),(7,1)]
  | 68 => some [(0,2),(1,5),(7,5)]
  | 69 => some [(0,3),(1,1),(6,0),(6,1)]
  | 70 => some [(0,0),(6,4)]
  | 71 => some [(1,2),(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(0,0),(4,0),(5,0),(8,0)]
  | 76 => some [(3,2),(4,5),(7,3)]
  | 77 => some [(4,0),(4,2),(7,0),(8,2)]
  | 78 => some [(0,3),(1,1),(4,3),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,0),(6,5)]
  | 81 => some [(0,4),(1,1),(7,1)]
  | 82 => some [(1,5),(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,1),(6,4)]
  | 84 => some [(1,2),(5,1),(6,2),(7,2)]
  | 85 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2),(8,5)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node1Domains1_fast_eq : root4Node1Domains1 = expandDomains root4Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node1Domains1 v = expandDomains root4Node1Domains1Fast v from by decide) v
theorem root4Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows0_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows1_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows2_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows3_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows4_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows5_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows6_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows7_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_0⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_1⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_2⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_3⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_4⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table33Scope, table33Rows8_5⟩
      root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq (by decide)
theorem root4Node1Step1Narrowing_checked :
    checkNarrowing table33 root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkNarrowing_flatten table33Scope [table33Rows0_0,table33Rows0_1,table33Rows0_2,table33Rows0_3,table33Rows0_4,table33Rows0_5,table33Rows1_0,table33Rows1_1,table33Rows1_2,table33Rows1_3,table33Rows1_4,table33Rows1_5,table33Rows2_0,table33Rows2_1,table33Rows2_2,table33Rows2_3,table33Rows2_4,table33Rows2_5,table33Rows3_0,table33Rows3_1,table33Rows3_2,table33Rows3_3,table33Rows3_4,table33Rows3_5,table33Rows4_0,table33Rows4_1,table33Rows4_2,table33Rows4_3,table33Rows4_4,table33Rows4_5,table33Rows5_0,table33Rows5_1,table33Rows5_2,table33Rows5_3,table33Rows5_4,table33Rows5_5,table33Rows6_0,table33Rows6_1,table33Rows6_2,table33Rows6_3,table33Rows6_4,table33Rows6_5,table33Rows7_0,table33Rows7_1,table33Rows7_2,table33Rows7_3,table33Rows7_4,table33Rows7_5,table33Rows8_0,table33Rows8_1,table33Rows8_2,table33Rows8_3,table33Rows8_4,table33Rows8_5]
    root4Node1Domains0 root4Node1Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node1Step1Chunk0_0_checked, root4Node1Step1Chunk0_1_checked, root4Node1Step1Chunk0_2_checked, root4Node1Step1Chunk0_3_checked, root4Node1Step1Chunk0_4_checked, root4Node1Step1Chunk0_5_checked, root4Node1Step1Chunk1_0_checked, root4Node1Step1Chunk1_1_checked, root4Node1Step1Chunk1_2_checked, root4Node1Step1Chunk1_3_checked, root4Node1Step1Chunk1_4_checked, root4Node1Step1Chunk1_5_checked, root4Node1Step1Chunk2_0_checked, root4Node1Step1Chunk2_1_checked, root4Node1Step1Chunk2_2_checked, root4Node1Step1Chunk2_3_checked, root4Node1Step1Chunk2_4_checked, root4Node1Step1Chunk2_5_checked, root4Node1Step1Chunk3_0_checked, root4Node1Step1Chunk3_1_checked, root4Node1Step1Chunk3_2_checked, root4Node1Step1Chunk3_3_checked, root4Node1Step1Chunk3_4_checked, root4Node1Step1Chunk3_5_checked, root4Node1Step1Chunk4_0_checked, root4Node1Step1Chunk4_1_checked, root4Node1Step1Chunk4_2_checked, root4Node1Step1Chunk4_3_checked, root4Node1Step1Chunk4_4_checked, root4Node1Step1Chunk4_5_checked, root4Node1Step1Chunk5_0_checked, root4Node1Step1Chunk5_1_checked, root4Node1Step1Chunk5_2_checked, root4Node1Step1Chunk5_3_checked, root4Node1Step1Chunk5_4_checked, root4Node1Step1Chunk5_5_checked, root4Node1Step1Chunk6_0_checked, root4Node1Step1Chunk6_1_checked, root4Node1Step1Chunk6_2_checked, root4Node1Step1Chunk6_3_checked, root4Node1Step1Chunk6_4_checked, root4Node1Step1Chunk6_5_checked, root4Node1Step1Chunk7_0_checked, root4Node1Step1Chunk7_1_checked, root4Node1Step1Chunk7_2_checked, root4Node1Step1Chunk7_3_checked, root4Node1Step1Chunk7_4_checked, root4Node1Step1Chunk7_5_checked, root4Node1Step1Chunk8_0_checked, root4Node1Step1Chunk8_1_checked, root4Node1Step1Chunk8_2_checked, root4Node1Step1Chunk8_3_checked, root4Node1Step1Chunk8_4_checked, root4Node1Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node1Step1_checked :
    checkReplacement table33 root4Node1Domains0 root4Node1Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node1Domains0 root4Node1Domains1
    root4Node1Domains0Fast root4Node1Domains1Fast
    root4Node1Domains0_fast_eq root4Node1Domains1_fast_eq
    root4Node1Step1Narrowing_checked (by decide)
def root4Node1Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4),(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4),(8,4)]
  | 4 => [(0,0),(0,5),(1,3),(6,3)]
  | 5 => [(4,4),(7,2),(8,2)]
  | 6 => [(4,3),(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5),(6,5)]
  | 11 => [(0,4),(6,1)]
  | 12 => [(5,1),(5,4),(8,1)]
  | 13 => [(4,0),(7,4)]
  | 14 => [(1,3),(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3),(8,3)]
  | 20 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 21 => [(5,1),(8,1)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(1,4),(3,4),(7,4)]
  | 25 => [(0,5),(6,3)]
  | 26 => [(4,4),(7,2)]
  | 27 => [(1,4),(7,4)]
  | 28 => [(0,5),(6,3)]
  | 29 => [(2,0),(2,2),(2,4),(4,4),(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(1,0),(3,0),(7,0)]
  | 33 => [(2,1),(2,3),(2,5)]
  | 34 => [(0,2),(6,0)]
  | 35 => [(1,1),(7,1)]
  | 36 => [(4,1),(7,5)]
  | 37 => [(0,2),(6,0)]
  | 38 => [(1,1),(3,1),(7,1)]
  | 39 => [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0),(6,4)]
  | 44 => [(1,2),(3,2),(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2),(8,2)]
  | 48 => [(5,0),(8,0)]
  | 49 => [(4,5),(7,3),(8,3)]
  | 50 => [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0),(1,4),(6,4)]
  | 60 => [(0,5),(1,2),(7,2)]
  | 61 => [(5,0),(8,0)]
  | 62 => [(4,5),(7,3)]
  | 63 => [(4,2),(7,0)]
  | 64 => [(5,3),(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,0),(6,1)]
  | 70 => [(0,0),(6,4)]
  | 71 => [(1,2),(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3),(6,3)]
  | 74 => [(7,2),(8,2)]
  | 75 => [(4,0),(5,0),(8,0)]
  | 76 => [(4,5),(7,3)]
  | 77 => [(4,2),(7,0),(8,2)]
  | 78 => [(0,3),(1,1),(4,3),(6,1),(7,1)]
  | 79 => [(4,1),(7,5),(8,1)]
  | 80 => [(0,2),(6,5)]
  | 81 => [(0,4),(1,1)]
  | 82 => [(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,4)]
  | 84 => [(1,2),(6,2),(7,2)]
  | 85 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,2),(8,5)]
  | 87 => [(5,0),(7,0),(8,0)]
  | 88 => [(4,3),(4,5),(8,3)]
  | 89 => [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => [(0,3),(1,0),(6,1),(8,3)]
def root4Node1Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4),(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4),(8,4)]
  | 4 => some [(0,0),(0,5),(1,3),(6,3)]
  | 5 => some [(4,4),(7,2),(8,2)]
  | 6 => some [(4,3),(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5),(6,5)]
  | 11 => some [(0,4),(6,1)]
  | 12 => some [(5,1),(5,4),(8,1)]
  | 13 => some [(4,0),(7,4)]
  | 14 => some [(1,3),(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3),(8,3)]
  | 20 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 21 => some [(5,1),(8,1)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(1,4),(3,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(4,4),(7,2)]
  | 27 => some [(1,4),(7,4)]
  | 28 => some [(0,5),(6,3)]
  | 29 => some [(2,0),(2,2),(2,4),(4,4),(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(1,0),(3,0),(7,0)]
  | 33 => some [(2,1),(2,3),(2,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(4,1),(7,5)]
  | 37 => some [(0,2),(6,0)]
  | 38 => some [(1,1),(3,1),(7,1)]
  | 39 => some [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0),(6,4)]
  | 44 => some [(1,2),(3,2),(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2),(8,2)]
  | 48 => some [(5,0),(8,0)]
  | 49 => some [(4,5),(7,3),(8,3)]
  | 50 => some [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(5,0),(8,0)]
  | 62 => some [(4,5),(7,3)]
  | 63 => some [(4,2),(7,0)]
  | 64 => some [(5,3),(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0),(6,4)]
  | 71 => some [(1,2),(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(0,3),(1,1),(4,3),(6,1),(7,1)]
  | 79 => some [(4,1),(7,5),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,4)]
  | 84 => some [(1,2),(6,2),(7,2)]
  | 85 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,2),(8,5)]
  | 87 => some [(5,0),(7,0),(8,0)]
  | 88 => some [(4,3),(4,5),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,0),(7,5)]
  | _ => some [(0,3),(1,0),(6,1),(8,3)]
theorem root4Node1Domains2_fast_eq : root4Node1Domains2 = expandDomains root4Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node1Domains2 v = expandDomains root4Node1Domains2Fast v from by decide) v
theorem root4Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq (by decide)
theorem root4Node1Step2Narrowing_checked :
    checkNarrowing table46 root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkNarrowing_flatten table46Scope [table46Rows0_0,table46Rows0_1,table46Rows0_2,table46Rows0_3,table46Rows0_4,table46Rows0_5,table46Rows1_0,table46Rows1_1,table46Rows1_2,table46Rows1_3,table46Rows1_4,table46Rows1_5,table46Rows2_0,table46Rows2_1,table46Rows2_2,table46Rows2_3,table46Rows2_4,table46Rows2_5,table46Rows3_0,table46Rows3_1,table46Rows3_2,table46Rows3_3,table46Rows3_4,table46Rows3_5,table46Rows4_0,table46Rows4_1,table46Rows4_2,table46Rows4_3,table46Rows4_4,table46Rows4_5,table46Rows5_0,table46Rows5_1,table46Rows5_2,table46Rows5_3,table46Rows5_4,table46Rows5_5,table46Rows6_0,table46Rows6_1,table46Rows6_2,table46Rows6_3,table46Rows6_4,table46Rows6_5,table46Rows7_0,table46Rows7_1,table46Rows7_2,table46Rows7_3,table46Rows7_4,table46Rows7_5,table46Rows8_0,table46Rows8_1,table46Rows8_2,table46Rows8_3,table46Rows8_4,table46Rows8_5]
    root4Node1Domains1 root4Node1Domains2 (by
      simp only [List.all_cons, List.all_nil, root4Node1Step2Chunk0_0_checked, root4Node1Step2Chunk0_1_checked, root4Node1Step2Chunk0_2_checked, root4Node1Step2Chunk0_3_checked, root4Node1Step2Chunk0_4_checked, root4Node1Step2Chunk0_5_checked, root4Node1Step2Chunk1_0_checked, root4Node1Step2Chunk1_1_checked, root4Node1Step2Chunk1_2_checked, root4Node1Step2Chunk1_3_checked, root4Node1Step2Chunk1_4_checked, root4Node1Step2Chunk1_5_checked, root4Node1Step2Chunk2_0_checked, root4Node1Step2Chunk2_1_checked, root4Node1Step2Chunk2_2_checked, root4Node1Step2Chunk2_3_checked, root4Node1Step2Chunk2_4_checked, root4Node1Step2Chunk2_5_checked, root4Node1Step2Chunk3_0_checked, root4Node1Step2Chunk3_1_checked, root4Node1Step2Chunk3_2_checked, root4Node1Step2Chunk3_3_checked, root4Node1Step2Chunk3_4_checked, root4Node1Step2Chunk3_5_checked, root4Node1Step2Chunk4_0_checked, root4Node1Step2Chunk4_1_checked, root4Node1Step2Chunk4_2_checked, root4Node1Step2Chunk4_3_checked, root4Node1Step2Chunk4_4_checked, root4Node1Step2Chunk4_5_checked, root4Node1Step2Chunk5_0_checked, root4Node1Step2Chunk5_1_checked, root4Node1Step2Chunk5_2_checked, root4Node1Step2Chunk5_3_checked, root4Node1Step2Chunk5_4_checked, root4Node1Step2Chunk5_5_checked, root4Node1Step2Chunk6_0_checked, root4Node1Step2Chunk6_1_checked, root4Node1Step2Chunk6_2_checked, root4Node1Step2Chunk6_3_checked, root4Node1Step2Chunk6_4_checked, root4Node1Step2Chunk6_5_checked, root4Node1Step2Chunk7_0_checked, root4Node1Step2Chunk7_1_checked, root4Node1Step2Chunk7_2_checked, root4Node1Step2Chunk7_3_checked, root4Node1Step2Chunk7_4_checked, root4Node1Step2Chunk7_5_checked, root4Node1Step2Chunk8_0_checked, root4Node1Step2Chunk8_1_checked, root4Node1Step2Chunk8_2_checked, root4Node1Step2Chunk8_3_checked, root4Node1Step2Chunk8_4_checked, root4Node1Step2Chunk8_5_checked, Bool.true_and])
theorem root4Node1Step2_checked :
    checkReplacement table46 root4Node1Domains1 root4Node1Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root4Node1Domains1 root4Node1Domains2
    root4Node1Domains1Fast root4Node1Domains2Fast
    root4Node1Domains1_fast_eq root4Node1Domains2_fast_eq
    root4Node1Step2Narrowing_checked (by decide)
def root4Node1Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4),(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4),(8,4)]
  | 4 => [(0,0),(0,5),(1,3),(6,3)]
  | 5 => [(4,4),(7,2),(8,2)]
  | 6 => [(4,3),(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5),(6,5)]
  | 11 => [(0,4),(6,1)]
  | 12 => [(5,1),(5,4),(8,1)]
  | 13 => [(4,0),(7,4)]
  | 14 => [(1,3),(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3),(8,3)]
  | 20 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 21 => [(5,1),(8,1)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(1,4),(3,4),(7,4)]
  | 25 => [(0,5),(6,3)]
  | 26 => [(4,4),(7,2)]
  | 27 => [(1,4),(7,4)]
  | 28 => [(0,5),(6,3)]
  | 29 => [(2,0),(2,2),(2,4),(4,4),(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(1,0),(3,0),(7,0)]
  | 33 => [(2,1),(2,3),(2,5)]
  | 34 => [(0,2),(6,0)]
  | 35 => [(1,1),(7,1)]
  | 36 => [(4,1),(7,5)]
  | 37 => [(0,2),(6,0)]
  | 38 => [(1,1),(3,1),(7,1)]
  | 39 => [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0),(6,4)]
  | 44 => [(1,2),(3,2),(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2),(8,2)]
  | 48 => [(5,0),(8,0)]
  | 49 => [(4,5),(7,3),(8,3)]
  | 50 => [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0),(1,4),(6,4)]
  | 60 => [(0,5),(1,2),(7,2)]
  | 61 => [(5,0),(8,0)]
  | 62 => [(4,5),(7,3)]
  | 63 => [(4,2),(7,0)]
  | 64 => [(5,3),(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,0),(6,1)]
  | 70 => [(0,0),(6,4)]
  | 71 => [(1,2),(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3),(6,3)]
  | 74 => [(7,2),(8,2)]
  | 75 => [(4,0),(5,0),(8,0)]
  | 76 => [(4,5),(7,3)]
  | 77 => [(4,2),(7,0),(8,2)]
  | 78 => [(0,3),(6,1)]
  | 79 => [(4,1),(8,1)]
  | 80 => [(0,2),(6,5)]
  | 81 => [(0,4),(1,1)]
  | 82 => [(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,4)]
  | 84 => [(1,2),(6,2),(7,2)]
  | 85 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,5)]
  | 87 => [(7,0),(8,0)]
  | 88 => [(4,3),(8,3)]
  | 89 => [(1,5),(3,5),(5,5),(7,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root4Node1Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4),(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4),(8,4)]
  | 4 => some [(0,0),(0,5),(1,3),(6,3)]
  | 5 => some [(4,4),(7,2),(8,2)]
  | 6 => some [(4,3),(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5),(6,5)]
  | 11 => some [(0,4),(6,1)]
  | 12 => some [(5,1),(5,4),(8,1)]
  | 13 => some [(4,0),(7,4)]
  | 14 => some [(1,3),(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3),(8,3)]
  | 20 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 21 => some [(5,1),(8,1)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(1,4),(3,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(4,4),(7,2)]
  | 27 => some [(1,4),(7,4)]
  | 28 => some [(0,5),(6,3)]
  | 29 => some [(2,0),(2,2),(2,4),(4,4),(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(1,0),(3,0),(7,0)]
  | 33 => some [(2,1),(2,3),(2,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(4,1),(7,5)]
  | 37 => some [(0,2),(6,0)]
  | 38 => some [(1,1),(3,1),(7,1)]
  | 39 => some [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0),(6,4)]
  | 44 => some [(1,2),(3,2),(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2),(8,2)]
  | 48 => some [(5,0),(8,0)]
  | 49 => some [(4,5),(7,3),(8,3)]
  | 50 => some [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(5,0),(8,0)]
  | 62 => some [(4,5),(7,3)]
  | 63 => some [(4,2),(7,0)]
  | 64 => some [(5,3),(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0),(6,4)]
  | 71 => some [(1,2),(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(0,3),(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,4)]
  | 84 => some [(1,2),(6,2),(7,2)]
  | 85 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root4Node1Domains3_fast_eq : root4Node1Domains3 = expandDomains root4Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node1Domains3 v = expandDomains root4Node1Domains3Fast v from by decide) v
theorem root4Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq (by decide)
theorem root4Node1Step3Narrowing_checked :
    checkNarrowing table65 root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root4Node1Domains2 root4Node1Domains3 (by
      simp only [List.all_cons, List.all_nil, root4Node1Step3Chunk0_0_checked, root4Node1Step3Chunk0_1_checked, root4Node1Step3Chunk0_2_checked, root4Node1Step3Chunk0_3_checked, root4Node1Step3Chunk0_4_checked, root4Node1Step3Chunk0_5_checked, root4Node1Step3Chunk1_0_checked, root4Node1Step3Chunk1_1_checked, root4Node1Step3Chunk1_2_checked, root4Node1Step3Chunk1_3_checked, root4Node1Step3Chunk1_4_checked, root4Node1Step3Chunk1_5_checked, root4Node1Step3Chunk2_0_checked, root4Node1Step3Chunk2_1_checked, root4Node1Step3Chunk2_2_checked, root4Node1Step3Chunk2_3_checked, root4Node1Step3Chunk2_4_checked, root4Node1Step3Chunk2_5_checked, root4Node1Step3Chunk3_0_checked, root4Node1Step3Chunk3_1_checked, root4Node1Step3Chunk3_2_checked, root4Node1Step3Chunk3_3_checked, root4Node1Step3Chunk3_4_checked, root4Node1Step3Chunk3_5_checked, root4Node1Step3Chunk4_0_checked, root4Node1Step3Chunk4_1_checked, root4Node1Step3Chunk4_2_checked, root4Node1Step3Chunk4_3_checked, root4Node1Step3Chunk4_4_checked, root4Node1Step3Chunk4_5_checked, root4Node1Step3Chunk5_0_checked, root4Node1Step3Chunk5_1_checked, root4Node1Step3Chunk5_2_checked, root4Node1Step3Chunk5_3_checked, root4Node1Step3Chunk5_4_checked, root4Node1Step3Chunk5_5_checked, root4Node1Step3Chunk6_0_checked, root4Node1Step3Chunk6_1_checked, root4Node1Step3Chunk6_2_checked, root4Node1Step3Chunk6_3_checked, root4Node1Step3Chunk6_4_checked, root4Node1Step3Chunk6_5_checked, root4Node1Step3Chunk7_0_checked, root4Node1Step3Chunk7_1_checked, root4Node1Step3Chunk7_2_checked, root4Node1Step3Chunk7_3_checked, root4Node1Step3Chunk7_4_checked, root4Node1Step3Chunk7_5_checked, root4Node1Step3Chunk8_0_checked, root4Node1Step3Chunk8_1_checked, root4Node1Step3Chunk8_2_checked, root4Node1Step3Chunk8_3_checked, root4Node1Step3Chunk8_4_checked, root4Node1Step3Chunk8_5_checked, Bool.true_and])
theorem root4Node1Step3_checked :
    checkReplacement table65 root4Node1Domains2 root4Node1Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root4Node1Domains2 root4Node1Domains3
    root4Node1Domains2Fast root4Node1Domains3Fast
    root4Node1Domains2_fast_eq root4Node1Domains3_fast_eq
    root4Node1Step3Narrowing_checked (by decide)
def root4Node1Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4),(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4),(8,4)]
  | 4 => [(0,0),(1,3)]
  | 5 => [(7,2),(8,2)]
  | 6 => [(4,3),(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5),(6,5)]
  | 11 => [(0,4),(6,1)]
  | 12 => [(5,1),(5,4),(8,1)]
  | 13 => [(4,0),(7,4)]
  | 14 => [(1,3),(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(5,5),(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3),(8,3)]
  | 20 => [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 21 => [(5,1),(8,1)]
  | 22 => [(0,1),(6,5)]
  | 23 => [(0,4),(6,2)]
  | 24 => [(1,4),(3,4),(7,4)]
  | 25 => [(0,5),(6,3)]
  | 26 => [(4,4),(7,2)]
  | 27 => [(1,4),(7,4)]
  | 28 => [(0,5),(6,3)]
  | 29 => [(2,0),(2,2),(2,4),(4,4),(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(1,0),(3,0),(7,0)]
  | 33 => [(2,1),(2,3),(2,5)]
  | 34 => [(0,2),(6,0)]
  | 35 => [(1,1),(7,1)]
  | 36 => [(4,1),(7,5)]
  | 37 => [(0,2),(6,0)]
  | 38 => [(1,1),(3,1),(7,1)]
  | 39 => [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0),(6,4)]
  | 44 => [(1,2),(3,2),(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2),(8,2)]
  | 48 => [(5,0),(8,0)]
  | 49 => [(4,5),(7,3),(8,3)]
  | 50 => [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0),(1,4),(6,4)]
  | 60 => [(0,5),(1,2),(7,2)]
  | 61 => [(5,0),(8,0)]
  | 62 => [(4,5),(7,3)]
  | 63 => [(4,2),(7,0)]
  | 64 => [(5,3),(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(1,5),(7,5)]
  | 69 => [(0,3),(6,0),(6,1)]
  | 70 => [(0,0),(6,4)]
  | 71 => [(1,2),(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3),(6,3)]
  | 74 => [(7,2),(8,2)]
  | 75 => [(4,0),(5,0),(8,0)]
  | 76 => [(4,5),(7,3)]
  | 77 => [(4,2),(7,0),(8,2)]
  | 78 => [(0,3),(6,1)]
  | 79 => [(4,1),(8,1)]
  | 80 => [(0,2),(6,5)]
  | 81 => [(0,4),(1,1)]
  | 82 => [(5,1),(5,4)]
  | 83 => [(0,0),(0,1),(6,4)]
  | 84 => [(1,2),(6,2),(7,2)]
  | 85 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => [(5,2),(5,5),(8,5)]
  | 87 => [(7,0),(8,0)]
  | 88 => [(4,3),(8,3)]
  | 89 => [(1,5),(3,5),(5,5),(7,5)]
  | _ => [(0,3),(1,0),(6,1)]
def root4Node1Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4),(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4),(8,4)]
  | 4 => some [(0,0),(1,3)]
  | 5 => some [(7,2),(8,2)]
  | 6 => some [(4,3),(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5),(6,5)]
  | 11 => some [(0,4),(6,1)]
  | 12 => some [(5,1),(5,4),(8,1)]
  | 13 => some [(4,0),(7,4)]
  | 14 => some [(1,3),(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(5,5),(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3),(8,3)]
  | 20 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 21 => some [(5,1),(8,1)]
  | 22 => some [(0,1),(6,5)]
  | 23 => some [(0,4),(6,2)]
  | 24 => some [(1,4),(3,4),(7,4)]
  | 25 => some [(0,5),(6,3)]
  | 26 => some [(4,4),(7,2)]
  | 27 => some [(1,4),(7,4)]
  | 28 => some [(0,5),(6,3)]
  | 29 => some [(2,0),(2,2),(2,4),(4,4),(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(1,0),(3,0),(7,0)]
  | 33 => some [(2,1),(2,3),(2,5)]
  | 34 => some [(0,2),(6,0)]
  | 35 => some [(1,1),(7,1)]
  | 36 => some [(4,1),(7,5)]
  | 37 => some [(0,2),(6,0)]
  | 38 => some [(1,1),(3,1),(7,1)]
  | 39 => some [(0,1),(1,5),(4,1),(5,1),(6,5),(7,5),(8,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0),(6,4)]
  | 44 => some [(1,2),(3,2),(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2),(8,2)]
  | 48 => some [(5,0),(8,0)]
  | 49 => some [(4,5),(7,3),(8,3)]
  | 50 => some [(1,0),(4,2),(5,2),(5,5),(7,0),(8,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(5,0),(8,0)]
  | 62 => some [(4,5),(7,3)]
  | 63 => some [(4,2),(7,0)]
  | 64 => some [(5,3),(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0),(6,4)]
  | 71 => some [(1,2),(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(5,0),(8,0)]
  | 76 => some [(4,5),(7,3)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(0,3),(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,0),(0,1),(6,4)]
  | 84 => some [(1,2),(6,2),(7,2)]
  | 85 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(1,5),(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0),(6,1)]
theorem root4Node1Domains4_fast_eq : root4Node1Domains4 = expandDomains root4Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node1Domains4 v = expandDomains root4Node1Domains4Fast v from by decide) v
theorem root4Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq (by decide)
theorem root4Node1Step4Narrowing_checked :
    checkNarrowing table1 root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkNarrowing_flatten table1Scope [table1Rows0_0,table1Rows0_1,table1Rows0_2,table1Rows0_3,table1Rows0_4,table1Rows0_5,table1Rows1_0,table1Rows1_1,table1Rows1_2,table1Rows1_3,table1Rows1_4,table1Rows1_5,table1Rows2_0,table1Rows2_1,table1Rows2_2,table1Rows2_3,table1Rows2_4,table1Rows2_5,table1Rows3_0,table1Rows3_1,table1Rows3_2,table1Rows3_3,table1Rows3_4,table1Rows3_5,table1Rows4_0,table1Rows4_1,table1Rows4_2,table1Rows4_3,table1Rows4_4,table1Rows4_5,table1Rows5_0,table1Rows5_1,table1Rows5_2,table1Rows5_3,table1Rows5_4,table1Rows5_5,table1Rows6_0,table1Rows6_1,table1Rows6_2,table1Rows6_3,table1Rows6_4,table1Rows6_5,table1Rows7_0,table1Rows7_1,table1Rows7_2,table1Rows7_3,table1Rows7_4,table1Rows7_5,table1Rows8_0,table1Rows8_1,table1Rows8_2,table1Rows8_3,table1Rows8_4,table1Rows8_5]
    root4Node1Domains3 root4Node1Domains4 (by
      simp only [List.all_cons, List.all_nil, root4Node1Step4Chunk0_0_checked, root4Node1Step4Chunk0_1_checked, root4Node1Step4Chunk0_2_checked, root4Node1Step4Chunk0_3_checked, root4Node1Step4Chunk0_4_checked, root4Node1Step4Chunk0_5_checked, root4Node1Step4Chunk1_0_checked, root4Node1Step4Chunk1_1_checked, root4Node1Step4Chunk1_2_checked, root4Node1Step4Chunk1_3_checked, root4Node1Step4Chunk1_4_checked, root4Node1Step4Chunk1_5_checked, root4Node1Step4Chunk2_0_checked, root4Node1Step4Chunk2_1_checked, root4Node1Step4Chunk2_2_checked, root4Node1Step4Chunk2_3_checked, root4Node1Step4Chunk2_4_checked, root4Node1Step4Chunk2_5_checked, root4Node1Step4Chunk3_0_checked, root4Node1Step4Chunk3_1_checked, root4Node1Step4Chunk3_2_checked, root4Node1Step4Chunk3_3_checked, root4Node1Step4Chunk3_4_checked, root4Node1Step4Chunk3_5_checked, root4Node1Step4Chunk4_0_checked, root4Node1Step4Chunk4_1_checked, root4Node1Step4Chunk4_2_checked, root4Node1Step4Chunk4_3_checked, root4Node1Step4Chunk4_4_checked, root4Node1Step4Chunk4_5_checked, root4Node1Step4Chunk5_0_checked, root4Node1Step4Chunk5_1_checked, root4Node1Step4Chunk5_2_checked, root4Node1Step4Chunk5_3_checked, root4Node1Step4Chunk5_4_checked, root4Node1Step4Chunk5_5_checked, root4Node1Step4Chunk6_0_checked, root4Node1Step4Chunk6_1_checked, root4Node1Step4Chunk6_2_checked, root4Node1Step4Chunk6_3_checked, root4Node1Step4Chunk6_4_checked, root4Node1Step4Chunk6_5_checked, root4Node1Step4Chunk7_0_checked, root4Node1Step4Chunk7_1_checked, root4Node1Step4Chunk7_2_checked, root4Node1Step4Chunk7_3_checked, root4Node1Step4Chunk7_4_checked, root4Node1Step4Chunk7_5_checked, root4Node1Step4Chunk8_0_checked, root4Node1Step4Chunk8_1_checked, root4Node1Step4Chunk8_2_checked, root4Node1Step4Chunk8_3_checked, root4Node1Step4Chunk8_4_checked, root4Node1Step4Chunk8_5_checked, Bool.true_and])
theorem root4Node1Step4_checked :
    checkReplacement table1 root4Node1Domains3 root4Node1Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root4Node1Domains3 root4Node1Domains4
    root4Node1Domains3Fast root4Node1Domains4Fast
    root4Node1Domains3_fast_eq root4Node1Domains4_fast_eq
    root4Node1Step4Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
