module

public import SpectreFinite.RadiusFiveRoot7Part44
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node112Domains0 : Domains 91 State := restrict root7Node111Domains4 28 (7,3)
def root7Node112Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1),(5,1),(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(1,4),(6,4)]
  | 38 => some [(0,5),(1,2)]
  | 39 => some [(4,4),(8,4)]
  | 40 => some [(4,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3),(6,0)]
  | 49 => some [(7,1),(8,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2),(8,2)]
  | 59 => some [(5,0),(5,3),(8,0)]
  | 60 => some [(4,5),(5,5),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4),(5,4)]
  | 69 => some [(0,0),(0,5),(6,3),(6,4)]
  | 70 => some [(5,0),(5,3)]
  | 71 => some [(4,5),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5),(4,3)]
  | 77 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | 78 => some [(0,0),(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(6,3)]
  | 82 => some [(4,4),(7,2)]
  | 83 => some [(0,0),(1,4),(6,4),(7,4)]
  | 84 => some [(0,5),(1,2),(1,3),(6,3),(7,2)]
  | 85 => some [(1,1),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5)]
  | 87 => some [(0,2),(6,0)]
  | 88 => some [(1,1),(7,1)]
  | 89 => some [(1,5),(4,1),(7,5),(8,1)]
  | _ => some [(0,2),(0,3),(6,0),(6,1),(6,5)]
theorem root7Node112Domains0_fast_eq : root7Node112Domains0 = expandDomains root7Node112Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node112Domains0 v = expandDomains root7Node112Domains0Fast v from by decide) v
def root7Node112Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1),(5,1),(8,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2),(5,5)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(4,4),(8,4)]
  | 40 => [(4,0),(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5),(7,5)]
  | 51 => [(0,1),(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(5,5),(8,5)]
  | 61 => [(0,3),(1,0)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(1,4),(3,4)]
  | 69 => [(0,5),(6,3)]
  | 70 => [(5,0),(5,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(3,0),(7,0)]
  | 76 => [(2,3),(2,5)]
  | 77 => [(0,2),(6,0)]
  | 78 => [(0,0),(0,5),(6,3)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(1,1),(6,1),(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node112Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1),(5,1),(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(4,4),(8,4)]
  | 40 => some [(4,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(5,5),(8,5)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4)]
  | 69 => some [(0,5),(6,3)]
  | 70 => some [(5,0),(5,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5)]
  | 77 => some [(0,2),(6,0)]
  | 78 => some [(0,0),(0,5),(6,3)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(1,1),(6,1),(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node112Domains1_fast_eq : root7Node112Domains1 = expandDomains root7Node112Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node112Domains1 v = expandDomains root7Node112Domains1Fast v from by decide) v
theorem root7Node112Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq (by decide)
theorem root7Node112Step1Narrowing_checked :
    checkNarrowing table56 root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node112Domains0 root7Node112Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node112Step1Chunk0_0_checked, root7Node112Step1Chunk0_1_checked, root7Node112Step1Chunk0_2_checked, root7Node112Step1Chunk0_3_checked, root7Node112Step1Chunk0_4_checked, root7Node112Step1Chunk0_5_checked, root7Node112Step1Chunk1_0_checked, root7Node112Step1Chunk1_1_checked, root7Node112Step1Chunk1_2_checked, root7Node112Step1Chunk1_3_checked, root7Node112Step1Chunk1_4_checked, root7Node112Step1Chunk1_5_checked, root7Node112Step1Chunk2_0_checked, root7Node112Step1Chunk2_1_checked, root7Node112Step1Chunk2_2_checked, root7Node112Step1Chunk2_3_checked, root7Node112Step1Chunk2_4_checked, root7Node112Step1Chunk2_5_checked, root7Node112Step1Chunk3_0_checked, root7Node112Step1Chunk3_1_checked, root7Node112Step1Chunk3_2_checked, root7Node112Step1Chunk3_3_checked, root7Node112Step1Chunk3_4_checked, root7Node112Step1Chunk3_5_checked, root7Node112Step1Chunk4_0_checked, root7Node112Step1Chunk4_1_checked, root7Node112Step1Chunk4_2_checked, root7Node112Step1Chunk4_3_checked, root7Node112Step1Chunk4_4_checked, root7Node112Step1Chunk4_5_checked, root7Node112Step1Chunk5_0_checked, root7Node112Step1Chunk5_1_checked, root7Node112Step1Chunk5_2_checked, root7Node112Step1Chunk5_3_checked, root7Node112Step1Chunk5_4_checked, root7Node112Step1Chunk5_5_checked, root7Node112Step1Chunk6_0_checked, root7Node112Step1Chunk6_1_checked, root7Node112Step1Chunk6_2_checked, root7Node112Step1Chunk6_3_checked, root7Node112Step1Chunk6_4_checked, root7Node112Step1Chunk6_5_checked, root7Node112Step1Chunk7_0_checked, root7Node112Step1Chunk7_1_checked, root7Node112Step1Chunk7_2_checked, root7Node112Step1Chunk7_3_checked, root7Node112Step1Chunk7_4_checked, root7Node112Step1Chunk7_5_checked, root7Node112Step1Chunk8_0_checked, root7Node112Step1Chunk8_1_checked, root7Node112Step1Chunk8_2_checked, root7Node112Step1Chunk8_3_checked, root7Node112Step1Chunk8_4_checked, root7Node112Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node112Step1_checked :
    checkReplacement table56 root7Node112Domains0 root7Node112Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node112Domains0 root7Node112Domains1
    root7Node112Domains0Fast root7Node112Domains1Fast
    root7Node112Domains0_fast_eq root7Node112Domains1_fast_eq
    root7Node112Step1Narrowing_checked (by decide)
def root7Node112Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1),(5,1),(8,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2),(5,5)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(4,4),(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5),(7,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(5,5),(8,5)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(1,4),(3,4)]
  | 69 => [(0,5),(6,3)]
  | 70 => [(5,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(3,0),(7,0)]
  | 76 => [(2,3),(2,5)]
  | 77 => [(0,2),(6,0)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node112Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1),(5,1),(8,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(5,5)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(4,4),(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(5,5),(8,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4)]
  | 69 => some [(0,5),(6,3)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5)]
  | 77 => some [(0,2),(6,0)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node112Domains2_fast_eq : root7Node112Domains2 = expandDomains root7Node112Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node112Domains2 v = expandDomains root7Node112Domains2Fast v from by decide) v
theorem root7Node112Step2Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq (by decide)
theorem root7Node112Step2Narrowing_checked :
    checkNarrowing table51 root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root7Node112Domains1 root7Node112Domains2 (by
      simp only [List.all_cons, List.all_nil, root7Node112Step2Chunk0_0_checked, root7Node112Step2Chunk0_1_checked, root7Node112Step2Chunk0_2_checked, root7Node112Step2Chunk0_3_checked, root7Node112Step2Chunk0_4_checked, root7Node112Step2Chunk0_5_checked, root7Node112Step2Chunk1_0_checked, root7Node112Step2Chunk1_1_checked, root7Node112Step2Chunk1_2_checked, root7Node112Step2Chunk1_3_checked, root7Node112Step2Chunk1_4_checked, root7Node112Step2Chunk1_5_checked, root7Node112Step2Chunk2_0_checked, root7Node112Step2Chunk2_1_checked, root7Node112Step2Chunk2_2_checked, root7Node112Step2Chunk2_3_checked, root7Node112Step2Chunk2_4_checked, root7Node112Step2Chunk2_5_checked, root7Node112Step2Chunk3_0_checked, root7Node112Step2Chunk3_1_checked, root7Node112Step2Chunk3_2_checked, root7Node112Step2Chunk3_3_checked, root7Node112Step2Chunk3_4_checked, root7Node112Step2Chunk3_5_checked, root7Node112Step2Chunk4_0_checked, root7Node112Step2Chunk4_1_checked, root7Node112Step2Chunk4_2_checked, root7Node112Step2Chunk4_3_checked, root7Node112Step2Chunk4_4_checked, root7Node112Step2Chunk4_5_checked, root7Node112Step2Chunk5_0_checked, root7Node112Step2Chunk5_1_checked, root7Node112Step2Chunk5_2_checked, root7Node112Step2Chunk5_3_checked, root7Node112Step2Chunk5_4_checked, root7Node112Step2Chunk5_5_checked, root7Node112Step2Chunk6_0_checked, root7Node112Step2Chunk6_1_checked, root7Node112Step2Chunk6_2_checked, root7Node112Step2Chunk6_3_checked, root7Node112Step2Chunk6_4_checked, root7Node112Step2Chunk6_5_checked, root7Node112Step2Chunk7_0_checked, root7Node112Step2Chunk7_1_checked, root7Node112Step2Chunk7_2_checked, root7Node112Step2Chunk7_3_checked, root7Node112Step2Chunk7_4_checked, root7Node112Step2Chunk7_5_checked, root7Node112Step2Chunk8_0_checked, root7Node112Step2Chunk8_1_checked, root7Node112Step2Chunk8_2_checked, root7Node112Step2Chunk8_3_checked, root7Node112Step2Chunk8_4_checked, root7Node112Step2Chunk8_5_checked, Bool.true_and])
theorem root7Node112Step2_checked :
    checkReplacement table51 root7Node112Domains1 root7Node112Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root7Node112Domains1 root7Node112Domains2
    root7Node112Domains1Fast root7Node112Domains2Fast
    root7Node112Domains1_fast_eq root7Node112Domains2_fast_eq
    root7Node112Step2Narrowing_checked (by decide)
def root7Node112Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(5,5),(8,5)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(1,4),(3,4)]
  | 69 => [(0,5),(6,3)]
  | 70 => [(5,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(3,0),(7,0)]
  | 76 => [(2,3),(2,5)]
  | 77 => [(0,2),(6,0)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(0,0),(6,4)]
  | 84 => [(1,2),(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5),(7,5)]
  | _ => [(0,3),(6,1)]
def root7Node112Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(5,5),(8,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4)]
  | 69 => some [(0,5),(6,3)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5)]
  | 77 => some [(0,2),(6,0)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node112Domains3_fast_eq : root7Node112Domains3 = expandDomains root7Node112Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node112Domains3 v = expandDomains root7Node112Domains3Fast v from by decide) v
theorem root7Node112Step3Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq (by decide)
theorem root7Node112Step3Narrowing_checked :
    checkNarrowing table12 root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root7Node112Domains2 root7Node112Domains3 (by
      simp only [List.all_cons, List.all_nil, root7Node112Step3Chunk0_0_checked, root7Node112Step3Chunk0_1_checked, root7Node112Step3Chunk0_2_checked, root7Node112Step3Chunk0_3_checked, root7Node112Step3Chunk0_4_checked, root7Node112Step3Chunk0_5_checked, root7Node112Step3Chunk1_0_checked, root7Node112Step3Chunk1_1_checked, root7Node112Step3Chunk1_2_checked, root7Node112Step3Chunk1_3_checked, root7Node112Step3Chunk1_4_checked, root7Node112Step3Chunk1_5_checked, root7Node112Step3Chunk2_0_checked, root7Node112Step3Chunk2_1_checked, root7Node112Step3Chunk2_2_checked, root7Node112Step3Chunk2_3_checked, root7Node112Step3Chunk2_4_checked, root7Node112Step3Chunk2_5_checked, root7Node112Step3Chunk3_0_checked, root7Node112Step3Chunk3_1_checked, root7Node112Step3Chunk3_2_checked, root7Node112Step3Chunk3_3_checked, root7Node112Step3Chunk3_4_checked, root7Node112Step3Chunk3_5_checked, root7Node112Step3Chunk4_0_checked, root7Node112Step3Chunk4_1_checked, root7Node112Step3Chunk4_2_checked, root7Node112Step3Chunk4_3_checked, root7Node112Step3Chunk4_4_checked, root7Node112Step3Chunk4_5_checked, root7Node112Step3Chunk5_0_checked, root7Node112Step3Chunk5_1_checked, root7Node112Step3Chunk5_2_checked, root7Node112Step3Chunk5_3_checked, root7Node112Step3Chunk5_4_checked, root7Node112Step3Chunk5_5_checked, root7Node112Step3Chunk6_0_checked, root7Node112Step3Chunk6_1_checked, root7Node112Step3Chunk6_2_checked, root7Node112Step3Chunk6_3_checked, root7Node112Step3Chunk6_4_checked, root7Node112Step3Chunk6_5_checked, root7Node112Step3Chunk7_0_checked, root7Node112Step3Chunk7_1_checked, root7Node112Step3Chunk7_2_checked, root7Node112Step3Chunk7_3_checked, root7Node112Step3Chunk7_4_checked, root7Node112Step3Chunk7_5_checked, root7Node112Step3Chunk8_0_checked, root7Node112Step3Chunk8_1_checked, root7Node112Step3Chunk8_2_checked, root7Node112Step3Chunk8_3_checked, root7Node112Step3Chunk8_4_checked, root7Node112Step3Chunk8_5_checked, Bool.true_and])
theorem root7Node112Step3_checked :
    checkReplacement table12 root7Node112Domains2 root7Node112Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root7Node112Domains2 root7Node112Domains3
    root7Node112Domains2Fast root7Node112Domains3Fast
    root7Node112Domains2_fast_eq root7Node112Domains3_fast_eq
    root7Node112Step3Narrowing_checked (by decide)
def root7Node113Domains0 : Domains 91 State := restrict root7Node112Domains3 60 (5,5)
def root7Node113Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(5,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4),(3,4)]
  | 69 => some [(0,5),(6,3)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0),(7,0)]
  | 76 => some [(2,3),(2,5)]
  | 77 => some [(0,2),(6,0)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0),(6,4)]
  | 84 => some [(1,2),(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5),(7,5)]
  | _ => some [(0,3),(6,1)]
theorem root7Node113Domains0_fast_eq : root7Node113Domains0 = expandDomains root7Node113Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node113Domains0 v = expandDomains root7Node113Domains0Fast v from by decide) v
def root7Node113Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(8,0)]
  | 2 => [(7,3)]
  | 3 => [(4,2)]
  | 4 => [(5,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(6,4)]
  | 9 => [(1,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(3,5)]
  | 16 => [(0,3)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(4,4)]
  | 22 => [(1,4)]
  | 23 => [(0,5)]
  | 24 => [(2,4)]
  | 25 => [(1,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(7,1)]
  | 31 => [(7,5)]
  | 32 => [(6,0)]
  | 33 => [(7,1)]
  | 34 => [(6,5)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(6,4)]
  | 38 => [(1,2)]
  | 39 => [(8,4)]
  | 40 => [(8,0)]
  | 41 => [(7,3)]
  | 42 => [(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(7,0)]
  | 46 => [(4,3)]
  | 47 => [(7,5)]
  | 48 => [(0,3)]
  | 49 => [(8,1)]
  | 50 => [(1,5)]
  | 51 => [(6,4)]
  | 52 => [(1,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(7,4)]
  | 57 => [(1,3)]
  | 58 => [(4,2)]
  | 59 => [(5,3)]
  | 60 => [(5,5)]
  | 61 => [(0,3)]
  | 62 => [(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(8,1)]
  | 66 => [(6,5)]
  | 67 => [(0,4)]
  | 68 => [(1,4)]
  | 69 => [(0,5)]
  | 70 => [(5,3)]
  | 71 => [(5,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5)]
  | 75 => [(3,0)]
  | 76 => [(2,5)]
  | 77 => [(6,0)]
  | 78 => [(0,5)]
  | 79 => [(4,4)]
  | 80 => [(1,4)]
  | 81 => [(0,5)]
  | 82 => [(4,4)]
  | 83 => [(0,0)]
  | 84 => [(7,2)]
  | 85 => [(7,1)]
  | 86 => [(7,5)]
  | 87 => [(6,0)]
  | 88 => [(7,1)]
  | 89 => [(1,5)]
  | _ => [(6,1)]
def root7Node113Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(8,0)]
  | 2 => some [(7,3)]
  | 3 => some [(4,2)]
  | 4 => some [(5,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(6,4)]
  | 9 => some [(1,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(3,5)]
  | 16 => some [(0,3)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(4,4)]
  | 22 => some [(1,4)]
  | 23 => some [(0,5)]
  | 24 => some [(2,4)]
  | 25 => some [(1,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(7,1)]
  | 31 => some [(7,5)]
  | 32 => some [(6,0)]
  | 33 => some [(7,1)]
  | 34 => some [(6,5)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(6,4)]
  | 38 => some [(1,2)]
  | 39 => some [(8,4)]
  | 40 => some [(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(7,0)]
  | 46 => some [(4,3)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3)]
  | 49 => some [(8,1)]
  | 50 => some [(1,5)]
  | 51 => some [(6,4)]
  | 52 => some [(1,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(7,4)]
  | 57 => some [(1,3)]
  | 58 => some [(4,2)]
  | 59 => some [(5,3)]
  | 60 => some [(5,5)]
  | 61 => some [(0,3)]
  | 62 => some [(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(8,1)]
  | 66 => some [(6,5)]
  | 67 => some [(0,4)]
  | 68 => some [(1,4)]
  | 69 => some [(0,5)]
  | 70 => some [(5,3)]
  | 71 => some [(5,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5)]
  | 75 => some [(3,0)]
  | 76 => some [(2,5)]
  | 77 => some [(6,0)]
  | 78 => some [(0,5)]
  | 79 => some [(4,4)]
  | 80 => some [(1,4)]
  | 81 => some [(0,5)]
  | 82 => some [(4,4)]
  | 83 => some [(0,0)]
  | 84 => some [(7,2)]
  | 85 => some [(7,1)]
  | 86 => some [(7,5)]
  | 87 => some [(6,0)]
  | 88 => some [(7,1)]
  | 89 => some [(1,5)]
  | _ => some [(6,1)]
theorem root7Node113Domains1_fast_eq : root7Node113Domains1 = expandDomains root7Node113Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root7Node113Domains1 v = expandDomains root7Node113Domains1Fast v from by decide) v
theorem root7Node113Step1Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Narrowing_checked :
    checkNarrowing table56 root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root7Node113Domains0 root7Node113Domains1 (by
      simp only [List.all_cons, List.all_nil, root7Node113Step1Chunk0_0_checked, root7Node113Step1Chunk0_1_checked, root7Node113Step1Chunk0_2_checked, root7Node113Step1Chunk0_3_checked, root7Node113Step1Chunk0_4_checked, root7Node113Step1Chunk0_5_checked, root7Node113Step1Chunk1_0_checked, root7Node113Step1Chunk1_1_checked, root7Node113Step1Chunk1_2_checked, root7Node113Step1Chunk1_3_checked, root7Node113Step1Chunk1_4_checked, root7Node113Step1Chunk1_5_checked, root7Node113Step1Chunk2_0_checked, root7Node113Step1Chunk2_1_checked, root7Node113Step1Chunk2_2_checked, root7Node113Step1Chunk2_3_checked, root7Node113Step1Chunk2_4_checked, root7Node113Step1Chunk2_5_checked, root7Node113Step1Chunk3_0_checked, root7Node113Step1Chunk3_1_checked, root7Node113Step1Chunk3_2_checked, root7Node113Step1Chunk3_3_checked, root7Node113Step1Chunk3_4_checked, root7Node113Step1Chunk3_5_checked, root7Node113Step1Chunk4_0_checked, root7Node113Step1Chunk4_1_checked, root7Node113Step1Chunk4_2_checked, root7Node113Step1Chunk4_3_checked, root7Node113Step1Chunk4_4_checked, root7Node113Step1Chunk4_5_checked, root7Node113Step1Chunk5_0_checked, root7Node113Step1Chunk5_1_checked, root7Node113Step1Chunk5_2_checked, root7Node113Step1Chunk5_3_checked, root7Node113Step1Chunk5_4_checked, root7Node113Step1Chunk5_5_checked, root7Node113Step1Chunk6_0_checked, root7Node113Step1Chunk6_1_checked, root7Node113Step1Chunk6_2_checked, root7Node113Step1Chunk6_3_checked, root7Node113Step1Chunk6_4_checked, root7Node113Step1Chunk6_5_checked, root7Node113Step1Chunk7_0_checked, root7Node113Step1Chunk7_1_checked, root7Node113Step1Chunk7_2_checked, root7Node113Step1Chunk7_3_checked, root7Node113Step1Chunk7_4_checked, root7Node113Step1Chunk7_5_checked, root7Node113Step1Chunk8_0_checked, root7Node113Step1Chunk8_1_checked, root7Node113Step1Chunk8_2_checked, root7Node113Step1Chunk8_3_checked, root7Node113Step1Chunk8_4_checked, root7Node113Step1Chunk8_5_checked, Bool.true_and])
theorem root7Node113Step1_checked :
    checkReplacement table56 root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq
    root7Node113Step1Narrowing_checked (by decide)
theorem root7Node113Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node113Domains1 (.output 55) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
