module

public import SpectreFinite.RadiusFiveRoot8Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable13
public import SpectreFinite.RadiusFiveTable19
public import SpectreFinite.RadiusFiveTable25
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node1Domains0 : Domains 91 State := restrict root8Node0Domains4 35 (1,1)
def root8Node1Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(4,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3),(6,4)]
  | 2 => some [(1,2),(3,2),(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(4,0),(7,4),(8,4)]
  | 4 => some [(0,0),(0,5),(1,3),(6,3),(7,3)]
  | 5 => some [(4,2),(4,4),(5,2),(7,2),(8,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,1),(8,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 8 => some [(0,3),(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(5,1),(7,5),(8,1)]
  | 10 => some [(0,1),(0,2),(1,5),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 12 => some [(3,4),(4,1),(5,1),(5,4),(7,5),(8,1),(8,4)]
  | 13 => some [(0,0),(1,3),(3,3),(5,0),(5,3),(6,4),(7,3),(8,0)]
  | 14 => some [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(7,3),(8,5)]
  | 15 => some [(4,0),(4,2),(7,0),(8,0)]
  | 16 => some [(5,3),(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2),(8,5)]
  | 18 => some [(1,0),(7,0),(8,0)]
  | 19 => some [(2,3),(4,3),(7,1),(7,3),(8,3)]
  | 20 => some [(0,2),(1,5),(3,5),(4,2),(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 21 => some [(0,1),(1,4),(1,5),(3,4),(5,4),(6,5),(7,4),(7,5)]
  | 22 => some [(0,0),(0,3),(0,4),(0,5),(6,1),(6,2),(6,3),(6,4)]
  | 23 => some [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 24 => some [(0,1),(1,4),(7,4)]
  | 25 => some [(0,5),(6,2),(6,3)]
  | 26 => some [(4,4),(7,2),(8,4)]
  | 27 => some [(1,4),(4,0),(6,4),(7,4)]
  | 28 => some [(0,5),(1,2),(1,3),(6,3),(7,3)]
  | 29 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(4,4),(7,4),(8,2),(8,4)]
  | 30 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(7,3),(8,5)]
  | 31 => some [(0,2),(1,0),(1,5),(3,5),(4,2),(6,0),(7,0),(7,5)]
  | 32 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 33 => some [(4,1),(7,5),(8,5)]
  | 34 => some [(0,2),(1,0),(6,0)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(5,1),(7,5),(8,1)]
  | 37 => some [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 38 => some [(0,4),(1,1),(3,1),(5,1),(6,2),(7,1),(8,1)]
  | 39 => some [(0,1),(1,4),(1,5),(3,4),(5,4),(6,5),(7,4)]
  | 40 => some [(0,0),(1,4),(6,3),(6,4),(7,4)]
  | 41 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 42 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 43 => some [(1,3),(3,3),(7,3)]
  | 44 => some [(5,2),(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(4,2),(5,2),(5,5),(8,2)]
  | 48 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0)]
  | 51 => some [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 52 => some [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 60 => some [(0,5),(1,2),(3,2),(7,2),(8,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(4,1),(7,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5),(7,5)]
  | 69 => some [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 70 => some [(0,0),(0,5),(1,3),(6,3)]
  | 71 => some [(4,4),(7,2),(8,2)]
  | 72 => some [(1,4),(4,0),(7,4),(8,0)]
  | 73 => some [(0,5),(1,3),(6,3),(7,3)]
  | 74 => some [(2,2),(2,4),(4,2),(8,2)]
  | 75 => some [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0),(8,0),(8,2)]
  | 78 => some [(0,4),(1,1),(6,1),(7,1)]
  | 79 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(5,4),(6,5),(7,4),(8,4)]
  | 83 => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(4,3),(7,3),(8,3)]
  | 86 => some [(3,5),(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 87 => some [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(4,5),(7,1),(8,1)]
  | 89 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0),(7,5)]
  | _ => some [(0,3),(1,1),(4,3),(6,1),(7,1)]
theorem root8Node1Domains0_fast_eq : root8Node1Domains0 = expandDomains root8Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node1Domains0 v = expandDomains root8Node1Domains0Fast v from by decide) v
def root8Node1Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(8,4)]
  | 1 => [(0,0),(6,4)]
  | 2 => [(1,2),(3,2),(7,2)]
  | 3 => [(4,0),(7,4),(8,4)]
  | 4 => [(0,0),(1,3),(7,3)]
  | 5 => [(5,2),(7,2),(8,2)]
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
  | 30 => [(2,1),(2,3),(2,5),(4,3),(4,5),(7,3),(8,5)]
  | 31 => [(0,2),(1,5),(3,5),(7,5)]
  | 32 => [(0,3),(1,1),(6,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(5,1),(8,1)]
  | 37 => [(0,1),(0,2),(6,5)]
  | 38 => [(0,4),(1,1),(6,2)]
  | 39 => [(0,1),(1,4),(1,5),(3,4),(5,4),(6,5),(7,4)]
  | 40 => [(0,0),(1,4),(6,3),(6,4),(7,4)]
  | 41 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 42 => [(2,0),(2,2),(2,4),(4,0)]
  | 43 => [(1,3),(3,3),(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(1,0),(3,0),(5,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0)]
  | 51 => [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 52 => [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 60 => [(0,5),(1,2),(3,2),(7,2),(8,2)]
  | 61 => [(5,0),(5,3),(8,3)]
  | 62 => [(4,5),(5,5),(8,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3),(6,0)]
  | 67 => [(7,1),(8,1)]
  | 68 => [(0,2),(1,5),(6,5),(7,5)]
  | 69 => [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 70 => [(0,0),(0,5),(1,3),(6,3)]
  | 71 => [(4,4),(7,2),(8,2)]
  | 72 => [(1,4),(4,0),(7,4),(8,0)]
  | 73 => [(0,5),(1,3),(6,3),(7,3)]
  | 74 => [(2,2),(2,4),(4,2),(8,2)]
  | 75 => [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 76 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 77 => [(4,2),(7,0),(8,0),(8,2)]
  | 78 => [(0,4),(1,1),(6,1),(7,1)]
  | 79 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(5,4),(6,5),(7,4),(8,4)]
  | 83 => [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 84 => [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(4,3),(7,3),(8,3)]
  | 86 => [(3,5),(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 87 => [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,3),(4,5),(7,1),(8,1)]
  | 89 => [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0),(7,5)]
  | _ => [(0,3),(1,1),(4,3),(6,1),(7,1)]
def root8Node1Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(8,4)]
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
  | 30 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(7,3),(8,5)]
  | 31 => some [(0,2),(1,5),(3,5),(7,5)]
  | 32 => some [(0,3),(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(5,1),(8,1)]
  | 37 => some [(0,1),(0,2),(6,5)]
  | 38 => some [(0,4),(1,1),(6,2)]
  | 39 => some [(0,1),(1,4),(1,5),(3,4),(5,4),(6,5),(7,4)]
  | 40 => some [(0,0),(1,4),(6,3),(6,4),(7,4)]
  | 41 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 42 => some [(2,0),(2,2),(2,4),(4,0)]
  | 43 => some [(1,3),(3,3),(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(1,0),(3,0),(5,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0)]
  | 51 => some [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 52 => some [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 60 => some [(0,5),(1,2),(3,2),(7,2),(8,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5),(7,5)]
  | 69 => some [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 70 => some [(0,0),(0,5),(1,3),(6,3)]
  | 71 => some [(4,4),(7,2),(8,2)]
  | 72 => some [(1,4),(4,0),(7,4),(8,0)]
  | 73 => some [(0,5),(1,3),(6,3),(7,3)]
  | 74 => some [(2,2),(2,4),(4,2),(8,2)]
  | 75 => some [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0),(8,0),(8,2)]
  | 78 => some [(0,4),(1,1),(6,1),(7,1)]
  | 79 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(5,4),(6,5),(7,4),(8,4)]
  | 83 => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(4,3),(7,3),(8,3)]
  | 86 => some [(3,5),(5,2),(5,5),(7,5),(8,2),(8,5)]
  | 87 => some [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(4,5),(7,1),(8,1)]
  | 89 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0),(7,5)]
  | _ => some [(0,3),(1,1),(4,3),(6,1),(7,1)]
theorem root8Node1Domains1_fast_eq : root8Node1Domains1 = expandDomains root8Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node1Domains1 v = expandDomains root8Node1Domains1Fast v from by decide) v
theorem root8Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Narrowing_checked :
    checkNarrowing table25 root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_flatten table25Scope [table25Rows0_0,table25Rows0_1,table25Rows0_2,table25Rows0_3,table25Rows0_4,table25Rows0_5,table25Rows1_0,table25Rows1_1,table25Rows1_2,table25Rows1_3,table25Rows1_4,table25Rows1_5,table25Rows2_0,table25Rows2_1,table25Rows2_2,table25Rows2_3,table25Rows2_4,table25Rows2_5,table25Rows3_0,table25Rows3_1,table25Rows3_2,table25Rows3_3,table25Rows3_4,table25Rows3_5,table25Rows4_0,table25Rows4_1,table25Rows4_2,table25Rows4_3,table25Rows4_4,table25Rows4_5,table25Rows5_0,table25Rows5_1,table25Rows5_2,table25Rows5_3,table25Rows5_4,table25Rows5_5,table25Rows6_0,table25Rows6_1,table25Rows6_2,table25Rows6_3,table25Rows6_4,table25Rows6_5,table25Rows7_0,table25Rows7_1,table25Rows7_2,table25Rows7_3,table25Rows7_4,table25Rows7_5,table25Rows8_0,table25Rows8_1,table25Rows8_2,table25Rows8_3,table25Rows8_4,table25Rows8_5]
    root8Node1Domains0 root8Node1Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node1Step1Chunk0_0_checked, root8Node1Step1Chunk0_1_checked, root8Node1Step1Chunk0_2_checked, root8Node1Step1Chunk0_3_checked, root8Node1Step1Chunk0_4_checked, root8Node1Step1Chunk0_5_checked, root8Node1Step1Chunk1_0_checked, root8Node1Step1Chunk1_1_checked, root8Node1Step1Chunk1_2_checked, root8Node1Step1Chunk1_3_checked, root8Node1Step1Chunk1_4_checked, root8Node1Step1Chunk1_5_checked, root8Node1Step1Chunk2_0_checked, root8Node1Step1Chunk2_1_checked, root8Node1Step1Chunk2_2_checked, root8Node1Step1Chunk2_3_checked, root8Node1Step1Chunk2_4_checked, root8Node1Step1Chunk2_5_checked, root8Node1Step1Chunk3_0_checked, root8Node1Step1Chunk3_1_checked, root8Node1Step1Chunk3_2_checked, root8Node1Step1Chunk3_3_checked, root8Node1Step1Chunk3_4_checked, root8Node1Step1Chunk3_5_checked, root8Node1Step1Chunk4_0_checked, root8Node1Step1Chunk4_1_checked, root8Node1Step1Chunk4_2_checked, root8Node1Step1Chunk4_3_checked, root8Node1Step1Chunk4_4_checked, root8Node1Step1Chunk4_5_checked, root8Node1Step1Chunk5_0_checked, root8Node1Step1Chunk5_1_checked, root8Node1Step1Chunk5_2_checked, root8Node1Step1Chunk5_3_checked, root8Node1Step1Chunk5_4_checked, root8Node1Step1Chunk5_5_checked, root8Node1Step1Chunk6_0_checked, root8Node1Step1Chunk6_1_checked, root8Node1Step1Chunk6_2_checked, root8Node1Step1Chunk6_3_checked, root8Node1Step1Chunk6_4_checked, root8Node1Step1Chunk6_5_checked, root8Node1Step1Chunk7_0_checked, root8Node1Step1Chunk7_1_checked, root8Node1Step1Chunk7_2_checked, root8Node1Step1Chunk7_3_checked, root8Node1Step1Chunk7_4_checked, root8Node1Step1Chunk7_5_checked, root8Node1Step1Chunk8_0_checked, root8Node1Step1Chunk8_1_checked, root8Node1Step1Chunk8_2_checked, root8Node1Step1Chunk8_3_checked, root8Node1Step1Chunk8_4_checked, root8Node1Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node1Step1_checked :
    checkReplacement table25 root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq
    root8Node1Step1Narrowing_checked (by decide)
def root8Node1Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(8,4)]
  | 1 => [(0,0),(6,4)]
  | 2 => [(1,2),(3,2),(7,2)]
  | 3 => [(4,0),(7,4),(8,4)]
  | 4 => [(0,0),(1,3),(7,3)]
  | 5 => [(5,2),(7,2),(8,2)]
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
  | 30 => [(2,1),(2,3),(2,5),(4,3),(4,5),(7,3),(8,5)]
  | 31 => [(0,2),(1,5),(3,5),(7,5)]
  | 32 => [(0,3),(1,1),(6,1)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1),(5,1),(8,1)]
  | 37 => [(0,1),(0,2),(6,5)]
  | 38 => [(0,4),(1,1),(6,2)]
  | 39 => [(0,1),(1,4),(1,5),(3,4),(5,4),(6,5),(7,4)]
  | 40 => [(0,0),(1,4),(6,3),(6,4),(7,4)]
  | 41 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 42 => [(2,0),(2,2),(2,4),(4,0)]
  | 43 => [(1,3),(3,3),(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(1,0),(3,0),(5,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0)]
  | 51 => [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 52 => [(1,1),(3,1),(5,1),(7,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(1,4),(6,4)]
  | 60 => [(0,5),(1,2),(3,2),(7,2),(8,2)]
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
def root8Node1Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(8,4)]
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
  | 30 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(7,3),(8,5)]
  | 31 => some [(0,2),(1,5),(3,5),(7,5)]
  | 32 => some [(0,3),(1,1),(6,1)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(5,1),(8,1)]
  | 37 => some [(0,1),(0,2),(6,5)]
  | 38 => some [(0,4),(1,1),(6,2)]
  | 39 => some [(0,1),(1,4),(1,5),(3,4),(5,4),(6,5),(7,4)]
  | 40 => some [(0,0),(1,4),(6,3),(6,4),(7,4)]
  | 41 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 42 => some [(2,0),(2,2),(2,4),(4,0)]
  | 43 => some [(1,3),(3,3),(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(1,0),(3,0),(5,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0)]
  | 51 => some [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 52 => some [(1,1),(3,1),(5,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(3,2),(7,2),(8,2)]
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
theorem root8Node1Domains2_fast_eq : root8Node1Domains2 = expandDomains root8Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node1Domains2 v = expandDomains root8Node1Domains2Fast v from by decide) v
theorem root8Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Narrowing_checked :
    checkNarrowing table65 root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root8Node1Domains1 root8Node1Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node1Step2Chunk0_0_checked, root8Node1Step2Chunk0_1_checked, root8Node1Step2Chunk0_2_checked, root8Node1Step2Chunk0_3_checked, root8Node1Step2Chunk0_4_checked, root8Node1Step2Chunk0_5_checked, root8Node1Step2Chunk1_0_checked, root8Node1Step2Chunk1_1_checked, root8Node1Step2Chunk1_2_checked, root8Node1Step2Chunk1_3_checked, root8Node1Step2Chunk1_4_checked, root8Node1Step2Chunk1_5_checked, root8Node1Step2Chunk2_0_checked, root8Node1Step2Chunk2_1_checked, root8Node1Step2Chunk2_2_checked, root8Node1Step2Chunk2_3_checked, root8Node1Step2Chunk2_4_checked, root8Node1Step2Chunk2_5_checked, root8Node1Step2Chunk3_0_checked, root8Node1Step2Chunk3_1_checked, root8Node1Step2Chunk3_2_checked, root8Node1Step2Chunk3_3_checked, root8Node1Step2Chunk3_4_checked, root8Node1Step2Chunk3_5_checked, root8Node1Step2Chunk4_0_checked, root8Node1Step2Chunk4_1_checked, root8Node1Step2Chunk4_2_checked, root8Node1Step2Chunk4_3_checked, root8Node1Step2Chunk4_4_checked, root8Node1Step2Chunk4_5_checked, root8Node1Step2Chunk5_0_checked, root8Node1Step2Chunk5_1_checked, root8Node1Step2Chunk5_2_checked, root8Node1Step2Chunk5_3_checked, root8Node1Step2Chunk5_4_checked, root8Node1Step2Chunk5_5_checked, root8Node1Step2Chunk6_0_checked, root8Node1Step2Chunk6_1_checked, root8Node1Step2Chunk6_2_checked, root8Node1Step2Chunk6_3_checked, root8Node1Step2Chunk6_4_checked, root8Node1Step2Chunk6_5_checked, root8Node1Step2Chunk7_0_checked, root8Node1Step2Chunk7_1_checked, root8Node1Step2Chunk7_2_checked, root8Node1Step2Chunk7_3_checked, root8Node1Step2Chunk7_4_checked, root8Node1Step2Chunk7_5_checked, root8Node1Step2Chunk8_0_checked, root8Node1Step2Chunk8_1_checked, root8Node1Step2Chunk8_2_checked, root8Node1Step2Chunk8_3_checked, root8Node1Step2Chunk8_4_checked, root8Node1Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node1Step2_checked :
    checkReplacement table65 root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq
    root8Node1Step2Narrowing_checked (by decide)
def root8Node1Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(8,4)]
  | 1 => [(0,0),(6,4)]
  | 2 => [(1,2),(3,2),(7,2)]
  | 3 => [(4,0),(7,4),(8,4)]
  | 4 => [(0,0),(1,3),(7,3)]
  | 5 => [(5,2),(7,2),(8,2)]
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
  | 39 => [(0,1),(1,4),(1,5),(3,4),(5,4),(6,5),(7,4)]
  | 40 => [(0,0),(1,4),(6,4),(7,4)]
  | 41 => [(0,5),(1,2),(3,2),(6,3)]
  | 42 => [(2,0),(2,2),(2,4),(4,0)]
  | 43 => [(1,3),(3,3),(7,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3),(8,3)]
  | 47 => [(5,2),(5,5)]
  | 48 => [(1,0),(3,0),(5,0),(7,0)]
  | 49 => [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0)]
  | 51 => [(0,2),(0,3),(6,0),(6,1)]
  | 52 => [(1,1),(3,1),(5,1),(7,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(1,4),(6,4)]
  | 57 => [(0,5),(1,2)]
  | 58 => [(4,4),(8,4)]
  | 59 => [(0,0),(1,4),(6,4)]
  | 60 => [(0,5),(1,2),(3,2),(7,2),(8,2)]
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
def root8Node1Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(8,4)]
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
  | 39 => some [(0,1),(1,4),(1,5),(3,4),(5,4),(6,5),(7,4)]
  | 40 => some [(0,0),(1,4),(6,4),(7,4)]
  | 41 => some [(0,5),(1,2),(3,2),(6,3)]
  | 42 => some [(2,0),(2,2),(2,4),(4,0)]
  | 43 => some [(1,3),(3,3),(7,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(1,0),(3,0),(5,0),(7,0)]
  | 49 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0)]
  | 51 => some [(0,2),(0,3),(6,0),(6,1)]
  | 52 => some [(1,1),(3,1),(5,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(3,2),(7,2),(8,2)]
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
theorem root8Node1Domains3_fast_eq : root8Node1Domains3 = expandDomains root8Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node1Domains3 v = expandDomains root8Node1Domains3Fast v from by decide) v
theorem root8Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Narrowing_checked :
    checkNarrowing table13 root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_flatten table13Scope [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5]
    root8Node1Domains2 root8Node1Domains3 (by
      simp only [List.all_cons, List.all_nil, root8Node1Step3Chunk0_0_checked, root8Node1Step3Chunk0_1_checked, root8Node1Step3Chunk0_2_checked, root8Node1Step3Chunk0_3_checked, root8Node1Step3Chunk0_4_checked, root8Node1Step3Chunk0_5_checked, root8Node1Step3Chunk1_0_checked, root8Node1Step3Chunk1_1_checked, root8Node1Step3Chunk1_2_checked, root8Node1Step3Chunk1_3_checked, root8Node1Step3Chunk1_4_checked, root8Node1Step3Chunk1_5_checked, root8Node1Step3Chunk2_0_checked, root8Node1Step3Chunk2_1_checked, root8Node1Step3Chunk2_2_checked, root8Node1Step3Chunk2_3_checked, root8Node1Step3Chunk2_4_checked, root8Node1Step3Chunk2_5_checked, root8Node1Step3Chunk3_0_checked, root8Node1Step3Chunk3_1_checked, root8Node1Step3Chunk3_2_checked, root8Node1Step3Chunk3_3_checked, root8Node1Step3Chunk3_4_checked, root8Node1Step3Chunk3_5_checked, root8Node1Step3Chunk4_0_checked, root8Node1Step3Chunk4_1_checked, root8Node1Step3Chunk4_2_checked, root8Node1Step3Chunk4_3_checked, root8Node1Step3Chunk4_4_checked, root8Node1Step3Chunk4_5_checked, root8Node1Step3Chunk5_0_checked, root8Node1Step3Chunk5_1_checked, root8Node1Step3Chunk5_2_checked, root8Node1Step3Chunk5_3_checked, root8Node1Step3Chunk5_4_checked, root8Node1Step3Chunk5_5_checked, root8Node1Step3Chunk6_0_checked, root8Node1Step3Chunk6_1_checked, root8Node1Step3Chunk6_2_checked, root8Node1Step3Chunk6_3_checked, root8Node1Step3Chunk6_4_checked, root8Node1Step3Chunk6_5_checked, root8Node1Step3Chunk7_0_checked, root8Node1Step3Chunk7_1_checked, root8Node1Step3Chunk7_2_checked, root8Node1Step3Chunk7_3_checked, root8Node1Step3Chunk7_4_checked, root8Node1Step3Chunk7_5_checked, root8Node1Step3Chunk8_0_checked, root8Node1Step3Chunk8_1_checked, root8Node1Step3Chunk8_2_checked, root8Node1Step3Chunk8_3_checked, root8Node1Step3Chunk8_4_checked, root8Node1Step3Chunk8_5_checked, Bool.true_and])
theorem root8Node1Step3_checked :
    checkReplacement table13 root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq
    root8Node1Step3Narrowing_checked (by decide)
def root8Node1Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(4,4),(8,4)]
  | 1 => [(0,0),(6,4)]
  | 2 => [(1,2),(3,2),(7,2)]
  | 3 => [(4,0),(7,4),(8,4)]
  | 4 => [(0,0),(1,3),(7,3)]
  | 5 => [(5,2),(7,2),(8,2)]
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
def root8Node1Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(4,4),(8,4)]
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
theorem root8Node1Domains4_fast_eq : root8Node1Domains4 = expandDomains root8Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node1Domains4 v = expandDomains root8Node1Domains4Fast v from by decide) v
theorem root8Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq (by decide)
theorem root8Node1Step4Narrowing_checked :
    checkNarrowing table19 root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkNarrowing_flatten table19Scope [table19Rows0_0,table19Rows0_1,table19Rows0_2,table19Rows0_3,table19Rows0_4,table19Rows0_5,table19Rows1_0,table19Rows1_1,table19Rows1_2,table19Rows1_3,table19Rows1_4,table19Rows1_5,table19Rows2_0,table19Rows2_1,table19Rows2_2,table19Rows2_3,table19Rows2_4,table19Rows2_5,table19Rows3_0,table19Rows3_1,table19Rows3_2,table19Rows3_3,table19Rows3_4,table19Rows3_5,table19Rows4_0,table19Rows4_1,table19Rows4_2,table19Rows4_3,table19Rows4_4,table19Rows4_5,table19Rows5_0,table19Rows5_1,table19Rows5_2,table19Rows5_3,table19Rows5_4,table19Rows5_5,table19Rows6_0,table19Rows6_1,table19Rows6_2,table19Rows6_3,table19Rows6_4,table19Rows6_5,table19Rows7_0,table19Rows7_1,table19Rows7_2,table19Rows7_3,table19Rows7_4,table19Rows7_5,table19Rows8_0,table19Rows8_1,table19Rows8_2,table19Rows8_3,table19Rows8_4,table19Rows8_5]
    root8Node1Domains3 root8Node1Domains4 (by
      simp only [List.all_cons, List.all_nil, root8Node1Step4Chunk0_0_checked, root8Node1Step4Chunk0_1_checked, root8Node1Step4Chunk0_2_checked, root8Node1Step4Chunk0_3_checked, root8Node1Step4Chunk0_4_checked, root8Node1Step4Chunk0_5_checked, root8Node1Step4Chunk1_0_checked, root8Node1Step4Chunk1_1_checked, root8Node1Step4Chunk1_2_checked, root8Node1Step4Chunk1_3_checked, root8Node1Step4Chunk1_4_checked, root8Node1Step4Chunk1_5_checked, root8Node1Step4Chunk2_0_checked, root8Node1Step4Chunk2_1_checked, root8Node1Step4Chunk2_2_checked, root8Node1Step4Chunk2_3_checked, root8Node1Step4Chunk2_4_checked, root8Node1Step4Chunk2_5_checked, root8Node1Step4Chunk3_0_checked, root8Node1Step4Chunk3_1_checked, root8Node1Step4Chunk3_2_checked, root8Node1Step4Chunk3_3_checked, root8Node1Step4Chunk3_4_checked, root8Node1Step4Chunk3_5_checked, root8Node1Step4Chunk4_0_checked, root8Node1Step4Chunk4_1_checked, root8Node1Step4Chunk4_2_checked, root8Node1Step4Chunk4_3_checked, root8Node1Step4Chunk4_4_checked, root8Node1Step4Chunk4_5_checked, root8Node1Step4Chunk5_0_checked, root8Node1Step4Chunk5_1_checked, root8Node1Step4Chunk5_2_checked, root8Node1Step4Chunk5_3_checked, root8Node1Step4Chunk5_4_checked, root8Node1Step4Chunk5_5_checked, root8Node1Step4Chunk6_0_checked, root8Node1Step4Chunk6_1_checked, root8Node1Step4Chunk6_2_checked, root8Node1Step4Chunk6_3_checked, root8Node1Step4Chunk6_4_checked, root8Node1Step4Chunk6_5_checked, root8Node1Step4Chunk7_0_checked, root8Node1Step4Chunk7_1_checked, root8Node1Step4Chunk7_2_checked, root8Node1Step4Chunk7_3_checked, root8Node1Step4Chunk7_4_checked, root8Node1Step4Chunk7_5_checked, root8Node1Step4Chunk8_0_checked, root8Node1Step4Chunk8_1_checked, root8Node1Step4Chunk8_2_checked, root8Node1Step4Chunk8_3_checked, root8Node1Step4Chunk8_4_checked, root8Node1Step4Chunk8_5_checked, Bool.true_and])
theorem root8Node1Step4_checked :
    checkReplacement table19 root8Node1Domains3 root8Node1Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root8Node1Domains3 root8Node1Domains4
    root8Node1Domains3Fast root8Node1Domains4Fast
    root8Node1Domains3_fast_eq root8Node1Domains4_fast_eq
    root8Node1Step4Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
