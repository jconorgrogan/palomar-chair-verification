module

public import SpectreFinite.RadiusFiveRoot0Part3
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node5Domains0 : Domains 91 State := restrict root0Node3Domains1 6 (8,5)
def root0Node5Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(0,0),(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2),(1,5)]
  | 22 => some [(1,1),(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2),(5,5)]
  | 31 => some [(7,0),(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,4),(0,5),(6,2)]
  | 41 => some [(4,4),(5,4),(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(8,0)]
  | 78 => some [(4,3),(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(4,5),(5,5),(8,5)]
  | 86 => some [(2,0),(7,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node5Domains0_fast_eq : root0Node5Domains0 = expandDomains root0Node5Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node5Domains0 v = expandDomains root0Node5Domains0Fast v from by decide) v
def root0Node5Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(8,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(1,5)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(8,5)]
  | 20 => [(7,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,4)]
  | 27 => [(6,3)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(5,2)]
  | 31 => [(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(1,0)]
  | 35 => [(2,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(4,1)]
  | 39 => [(0,2)]
  | 40 => [(0,4),(6,2)]
  | 41 => [(5,4),(8,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(5,2)]
  | 50 => [(8,0)]
  | 51 => [(4,3),(7,1)]
  | 52 => [(7,5)]
  | 53 => [(6,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(1,3),(7,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(0,4),(1,2),(6,2)]
  | 71 => [(5,4),(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3),(6,3)]
  | 76 => [(7,2),(8,2)]
  | 77 => [(4,0),(8,0)]
  | 78 => [(4,3),(7,1),(8,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(4,1),(8,1)]
  | 82 => [(0,2),(6,5)]
  | 83 => [(0,4),(1,1)]
  | 84 => [(5,1),(5,4)]
  | 85 => [(0,5),(4,5),(5,5),(8,5)]
  | 86 => [(2,0),(7,0)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(8,5)]
  | 89 => [(7,0),(8,0)]
  | _ => [(4,3),(8,3)]
def root0Node5Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,4),(6,2)]
  | 41 => some [(5,4),(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(8,0)]
  | 78 => some [(4,3),(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(4,5),(5,5),(8,5)]
  | 86 => some [(2,0),(7,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node5Domains1_fast_eq : root0Node5Domains1 = expandDomains root0Node5Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node5Domains1 v = expandDomains root0Node5Domains1Fast v from by decide) v
theorem root0Node5Step1Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq (by decide)
theorem root0Node5Step1Narrowing_checked :
    checkNarrowing table6 root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkNarrowing_flatten table6Scope [table6Rows0_0,table6Rows0_1,table6Rows0_2,table6Rows0_3,table6Rows0_4,table6Rows0_5,table6Rows1_0,table6Rows1_1,table6Rows1_2,table6Rows1_3,table6Rows1_4,table6Rows1_5,table6Rows2_0,table6Rows2_1,table6Rows2_2,table6Rows2_3,table6Rows2_4,table6Rows2_5,table6Rows3_0,table6Rows3_1,table6Rows3_2,table6Rows3_3,table6Rows3_4,table6Rows3_5,table6Rows4_0,table6Rows4_1,table6Rows4_2,table6Rows4_3,table6Rows4_4,table6Rows4_5,table6Rows5_0,table6Rows5_1,table6Rows5_2,table6Rows5_3,table6Rows5_4,table6Rows5_5,table6Rows6_0,table6Rows6_1,table6Rows6_2,table6Rows6_3,table6Rows6_4,table6Rows6_5,table6Rows7_0,table6Rows7_1,table6Rows7_2,table6Rows7_3,table6Rows7_4,table6Rows7_5,table6Rows8_0,table6Rows8_1,table6Rows8_2,table6Rows8_3,table6Rows8_4,table6Rows8_5]
    root0Node5Domains0 root0Node5Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node5Step1Chunk0_0_checked, root0Node5Step1Chunk0_1_checked, root0Node5Step1Chunk0_2_checked, root0Node5Step1Chunk0_3_checked, root0Node5Step1Chunk0_4_checked, root0Node5Step1Chunk0_5_checked, root0Node5Step1Chunk1_0_checked, root0Node5Step1Chunk1_1_checked, root0Node5Step1Chunk1_2_checked, root0Node5Step1Chunk1_3_checked, root0Node5Step1Chunk1_4_checked, root0Node5Step1Chunk1_5_checked, root0Node5Step1Chunk2_0_checked, root0Node5Step1Chunk2_1_checked, root0Node5Step1Chunk2_2_checked, root0Node5Step1Chunk2_3_checked, root0Node5Step1Chunk2_4_checked, root0Node5Step1Chunk2_5_checked, root0Node5Step1Chunk3_0_checked, root0Node5Step1Chunk3_1_checked, root0Node5Step1Chunk3_2_checked, root0Node5Step1Chunk3_3_checked, root0Node5Step1Chunk3_4_checked, root0Node5Step1Chunk3_5_checked, root0Node5Step1Chunk4_0_checked, root0Node5Step1Chunk4_1_checked, root0Node5Step1Chunk4_2_checked, root0Node5Step1Chunk4_3_checked, root0Node5Step1Chunk4_4_checked, root0Node5Step1Chunk4_5_checked, root0Node5Step1Chunk5_0_checked, root0Node5Step1Chunk5_1_checked, root0Node5Step1Chunk5_2_checked, root0Node5Step1Chunk5_3_checked, root0Node5Step1Chunk5_4_checked, root0Node5Step1Chunk5_5_checked, root0Node5Step1Chunk6_0_checked, root0Node5Step1Chunk6_1_checked, root0Node5Step1Chunk6_2_checked, root0Node5Step1Chunk6_3_checked, root0Node5Step1Chunk6_4_checked, root0Node5Step1Chunk6_5_checked, root0Node5Step1Chunk7_0_checked, root0Node5Step1Chunk7_1_checked, root0Node5Step1Chunk7_2_checked, root0Node5Step1Chunk7_3_checked, root0Node5Step1Chunk7_4_checked, root0Node5Step1Chunk7_5_checked, root0Node5Step1Chunk8_0_checked, root0Node5Step1Chunk8_1_checked, root0Node5Step1Chunk8_2_checked, root0Node5Step1Chunk8_3_checked, root0Node5Step1Chunk8_4_checked, root0Node5Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node5Step1_checked :
    checkReplacement table6 root0Node5Domains0 root0Node5Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node5Domains0 root0Node5Domains1
    root0Node5Domains0Fast root0Node5Domains1Fast
    root0Node5Domains0_fast_eq root0Node5Domains1_fast_eq
    root0Node5Step1Narrowing_checked (by decide)
def root0Node6Domains0 : Domains 91 State := restrict root0Node5Domains1 40 (0,4)
def root0Node6Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,4)]
  | 41 => some [(5,4),(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(8,0)]
  | 78 => some [(4,3),(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(4,5),(5,5),(8,5)]
  | 86 => some [(2,0),(7,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node6Domains0_fast_eq : root0Node6Domains0 = expandDomains root0Node6Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node6Domains0 v = expandDomains root0Node6Domains0Fast v from by decide) v
def root0Node6Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(8,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(1,5)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(8,5)]
  | 20 => [(7,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,4)]
  | 27 => [(6,3)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(5,2)]
  | 31 => [(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(1,0)]
  | 35 => [(2,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(4,1)]
  | 39 => [(0,2)]
  | 40 => [(0,4)]
  | 41 => [(5,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(5,2)]
  | 50 => [(8,0)]
  | 51 => [(4,3)]
  | 52 => [(7,5)]
  | 53 => [(6,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(1,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(0,4)]
  | 71 => [(5,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(6,3)]
  | 76 => [(7,2),(8,2)]
  | 77 => [(4,0),(8,0)]
  | 78 => [(4,3)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(4,1)]
  | 82 => [(0,2)]
  | 83 => [(0,4),(1,1)]
  | 84 => [(5,1),(5,4)]
  | 85 => [(0,5)]
  | 86 => [(2,0)]
  | 87 => [(7,3)]
  | 88 => [(5,2)]
  | 89 => [(7,0),(8,0)]
  | _ => [(4,3),(8,3)]
def root0Node6Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,4)]
  | 41 => some [(5,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(8,0)]
  | 51 => some [(4,3)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4)]
  | 71 => some [(5,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(8,0)]
  | 78 => some [(4,3)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1)]
  | 82 => some [(0,2)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5)]
  | 86 => some [(2,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node6Domains1_fast_eq : root0Node6Domains1 = expandDomains root0Node6Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node6Domains1 v = expandDomains root0Node6Domains1Fast v from by decide) v
theorem root0Node6Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq (by decide)
theorem root0Node6Step1Narrowing_checked :
    checkNarrowing table54 root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root0Node6Domains0 root0Node6Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node6Step1Chunk0_0_checked, root0Node6Step1Chunk0_1_checked, root0Node6Step1Chunk0_2_checked, root0Node6Step1Chunk0_3_checked, root0Node6Step1Chunk0_4_checked, root0Node6Step1Chunk0_5_checked, root0Node6Step1Chunk1_0_checked, root0Node6Step1Chunk1_1_checked, root0Node6Step1Chunk1_2_checked, root0Node6Step1Chunk1_3_checked, root0Node6Step1Chunk1_4_checked, root0Node6Step1Chunk1_5_checked, root0Node6Step1Chunk2_0_checked, root0Node6Step1Chunk2_1_checked, root0Node6Step1Chunk2_2_checked, root0Node6Step1Chunk2_3_checked, root0Node6Step1Chunk2_4_checked, root0Node6Step1Chunk2_5_checked, root0Node6Step1Chunk3_0_checked, root0Node6Step1Chunk3_1_checked, root0Node6Step1Chunk3_2_checked, root0Node6Step1Chunk3_3_checked, root0Node6Step1Chunk3_4_checked, root0Node6Step1Chunk3_5_checked, root0Node6Step1Chunk4_0_checked, root0Node6Step1Chunk4_1_checked, root0Node6Step1Chunk4_2_checked, root0Node6Step1Chunk4_3_checked, root0Node6Step1Chunk4_4_checked, root0Node6Step1Chunk4_5_checked, root0Node6Step1Chunk5_0_checked, root0Node6Step1Chunk5_1_checked, root0Node6Step1Chunk5_2_checked, root0Node6Step1Chunk5_3_checked, root0Node6Step1Chunk5_4_checked, root0Node6Step1Chunk5_5_checked, root0Node6Step1Chunk6_0_checked, root0Node6Step1Chunk6_1_checked, root0Node6Step1Chunk6_2_checked, root0Node6Step1Chunk6_3_checked, root0Node6Step1Chunk6_4_checked, root0Node6Step1Chunk6_5_checked, root0Node6Step1Chunk7_0_checked, root0Node6Step1Chunk7_1_checked, root0Node6Step1Chunk7_2_checked, root0Node6Step1Chunk7_3_checked, root0Node6Step1Chunk7_4_checked, root0Node6Step1Chunk7_5_checked, root0Node6Step1Chunk8_0_checked, root0Node6Step1Chunk8_1_checked, root0Node6Step1Chunk8_2_checked, root0Node6Step1Chunk8_3_checked, root0Node6Step1Chunk8_4_checked, root0Node6Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node6Step1_checked :
    checkReplacement table54 root0Node6Domains0 root0Node6Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node6Domains0 root0Node6Domains1
    root0Node6Domains0Fast root0Node6Domains1Fast
    root0Node6Domains0_fast_eq root0Node6Domains1_fast_eq
    root0Node6Step1Narrowing_checked (by decide)
def root0Node6Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(8,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(1,5)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(8,5)]
  | 20 => [(7,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,4)]
  | 27 => [(6,3)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(5,2)]
  | 31 => [(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(1,0)]
  | 35 => [(2,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(4,1)]
  | 39 => [(0,2)]
  | 40 => [(0,4)]
  | 41 => [(5,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(5,2)]
  | 50 => [(8,0)]
  | 51 => [(4,3)]
  | 52 => [(7,5)]
  | 53 => [(6,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(1,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(0,4)]
  | 71 => [(5,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(6,3)]
  | 76 => [(7,2)]
  | 77 => [(4,0)]
  | 78 => [(4,3)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(4,1)]
  | 82 => [(0,2)]
  | 83 => [(1,1)]
  | 84 => [(5,1)]
  | 85 => [(0,5)]
  | 86 => [(2,0)]
  | 87 => [(7,3)]
  | 88 => [(5,2)]
  | 89 => [(8,0)]
  | _ => [(8,3)]
def root0Node6Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(0,4)]
  | 41 => some [(5,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(8,0)]
  | 51 => some [(4,3)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4)]
  | 71 => some [(5,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(6,3)]
  | 76 => some [(7,2)]
  | 77 => some [(4,0)]
  | 78 => some [(4,3)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1)]
  | 82 => some [(0,2)]
  | 83 => some [(1,1)]
  | 84 => some [(5,1)]
  | 85 => some [(0,5)]
  | 86 => some [(2,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2)]
  | 89 => some [(8,0)]
  | _ => some [(8,3)]
theorem root0Node6Domains2_fast_eq : root0Node6Domains2 = expandDomains root0Node6Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node6Domains2 v = expandDomains root0Node6Domains2Fast v from by decide) v
theorem root0Node6Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq (by decide)
theorem root0Node6Step2Narrowing_checked :
    checkNarrowing table56 root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root0Node6Domains1 root0Node6Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node6Step2Chunk0_0_checked, root0Node6Step2Chunk0_1_checked, root0Node6Step2Chunk0_2_checked, root0Node6Step2Chunk0_3_checked, root0Node6Step2Chunk0_4_checked, root0Node6Step2Chunk0_5_checked, root0Node6Step2Chunk1_0_checked, root0Node6Step2Chunk1_1_checked, root0Node6Step2Chunk1_2_checked, root0Node6Step2Chunk1_3_checked, root0Node6Step2Chunk1_4_checked, root0Node6Step2Chunk1_5_checked, root0Node6Step2Chunk2_0_checked, root0Node6Step2Chunk2_1_checked, root0Node6Step2Chunk2_2_checked, root0Node6Step2Chunk2_3_checked, root0Node6Step2Chunk2_4_checked, root0Node6Step2Chunk2_5_checked, root0Node6Step2Chunk3_0_checked, root0Node6Step2Chunk3_1_checked, root0Node6Step2Chunk3_2_checked, root0Node6Step2Chunk3_3_checked, root0Node6Step2Chunk3_4_checked, root0Node6Step2Chunk3_5_checked, root0Node6Step2Chunk4_0_checked, root0Node6Step2Chunk4_1_checked, root0Node6Step2Chunk4_2_checked, root0Node6Step2Chunk4_3_checked, root0Node6Step2Chunk4_4_checked, root0Node6Step2Chunk4_5_checked, root0Node6Step2Chunk5_0_checked, root0Node6Step2Chunk5_1_checked, root0Node6Step2Chunk5_2_checked, root0Node6Step2Chunk5_3_checked, root0Node6Step2Chunk5_4_checked, root0Node6Step2Chunk5_5_checked, root0Node6Step2Chunk6_0_checked, root0Node6Step2Chunk6_1_checked, root0Node6Step2Chunk6_2_checked, root0Node6Step2Chunk6_3_checked, root0Node6Step2Chunk6_4_checked, root0Node6Step2Chunk6_5_checked, root0Node6Step2Chunk7_0_checked, root0Node6Step2Chunk7_1_checked, root0Node6Step2Chunk7_2_checked, root0Node6Step2Chunk7_3_checked, root0Node6Step2Chunk7_4_checked, root0Node6Step2Chunk7_5_checked, root0Node6Step2Chunk8_0_checked, root0Node6Step2Chunk8_1_checked, root0Node6Step2Chunk8_2_checked, root0Node6Step2Chunk8_3_checked, root0Node6Step2Chunk8_4_checked, root0Node6Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node6Step2_checked :
    checkReplacement table56 root0Node6Domains1 root0Node6Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node6Domains1 root0Node6Domains2
    root0Node6Domains1Fast root0Node6Domains2Fast
    root0Node6Domains1_fast_eq root0Node6Domains2_fast_eq
    root0Node6Step2Narrowing_checked (by decide)
theorem root0Node6Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node6Domains2 (.output 2) = true := by decide
def root0Node7Domains0 : Domains 91 State := restrict root0Node5Domains1 40 (6,2)
def root0Node7Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(6,2)]
  | 41 => some [(5,4),(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(8,0)]
  | 51 => some [(4,3),(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(5,4),(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(8,0)]
  | 78 => some [(4,3),(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(4,5),(5,5),(8,5)]
  | 86 => some [(2,0),(7,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node7Domains0_fast_eq : root0Node7Domains0 = expandDomains root0Node7Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node7Domains0 v = expandDomains root0Node7Domains0Fast v from by decide) v
def root0Node7Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1)]
  | 1 => [(6,2)]
  | 2 => [(8,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,4)]
  | 6 => [(8,5)]
  | 7 => [(1,0)]
  | 8 => [(7,1)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(8,1)]
  | 12 => [(1,5)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(4,0)]
  | 16 => [(7,3)]
  | 17 => [(4,2)]
  | 18 => [(5,3)]
  | 19 => [(8,5)]
  | 20 => [(7,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,4)]
  | 27 => [(6,3)]
  | 28 => [(7,2)]
  | 29 => [(7,4)]
  | 30 => [(5,2)]
  | 31 => [(8,0)]
  | 32 => [(8,3)]
  | 33 => [(5,5)]
  | 34 => [(1,0)]
  | 35 => [(2,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(4,1)]
  | 39 => [(0,2)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4)]
  | 43 => [(0,5)]
  | 44 => [(4,4)]
  | 45 => [(0,0)]
  | 46 => [(3,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(5,2)]
  | 50 => [(8,0)]
  | 51 => [(7,1)]
  | 52 => [(7,5)]
  | 53 => [(6,0)]
  | 54 => [(7,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(7,3)]
  | 62 => [(8,2)]
  | 63 => [(5,0)]
  | 64 => [(4,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(1,2),(6,2)]
  | 71 => [(8,4)]
  | 72 => [(0,0)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3)]
  | 76 => [(7,2),(8,2)]
  | 77 => [(4,0),(8,0)]
  | 78 => [(7,1),(8,1)]
  | 79 => [(1,5)]
  | 80 => [(6,1)]
  | 81 => [(8,1)]
  | 82 => [(6,5)]
  | 83 => [(0,4),(1,1)]
  | 84 => [(5,1),(5,4)]
  | 85 => [(4,5),(5,5),(8,5)]
  | 86 => [(7,0)]
  | 87 => [(8,3)]
  | 88 => [(5,5),(8,5)]
  | 89 => [(7,0),(8,0)]
  | _ => [(4,3),(8,3)]
def root0Node7Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1)]
  | 1 => some [(6,2)]
  | 2 => some [(8,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,4)]
  | 6 => some [(8,5)]
  | 7 => some [(1,0)]
  | 8 => some [(7,1)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(8,1)]
  | 12 => some [(1,5)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(4,0)]
  | 16 => some [(7,3)]
  | 17 => some [(4,2)]
  | 18 => some [(5,3)]
  | 19 => some [(8,5)]
  | 20 => some [(7,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,4)]
  | 27 => some [(6,3)]
  | 28 => some [(7,2)]
  | 29 => some [(7,4)]
  | 30 => some [(5,2)]
  | 31 => some [(8,0)]
  | 32 => some [(8,3)]
  | 33 => some [(5,5)]
  | 34 => some [(1,0)]
  | 35 => some [(2,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(4,1)]
  | 39 => some [(0,2)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(0,5)]
  | 44 => some [(4,4)]
  | 45 => some [(0,0)]
  | 46 => some [(3,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(5,2)]
  | 50 => some [(8,0)]
  | 51 => some [(7,1)]
  | 52 => some [(7,5)]
  | 53 => some [(6,0)]
  | 54 => some [(7,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(7,3)]
  | 62 => some [(8,2)]
  | 63 => some [(5,0)]
  | 64 => some [(4,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(1,2),(6,2)]
  | 71 => some [(8,4)]
  | 72 => some [(0,0)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(8,0)]
  | 78 => some [(7,1),(8,1)]
  | 79 => some [(1,5)]
  | 80 => some [(6,1)]
  | 81 => some [(8,1)]
  | 82 => some [(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(4,5),(5,5),(8,5)]
  | 86 => some [(7,0)]
  | 87 => some [(8,3)]
  | 88 => some [(5,5),(8,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node7Domains1_fast_eq : root0Node7Domains1 = expandDomains root0Node7Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node7Domains1 v = expandDomains root0Node7Domains1Fast v from by decide) v
theorem root0Node7Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq (by decide)
theorem root0Node7Step1Narrowing_checked :
    checkNarrowing table54 root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root0Node7Domains0 root0Node7Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node7Step1Chunk0_0_checked, root0Node7Step1Chunk0_1_checked, root0Node7Step1Chunk0_2_checked, root0Node7Step1Chunk0_3_checked, root0Node7Step1Chunk0_4_checked, root0Node7Step1Chunk0_5_checked, root0Node7Step1Chunk1_0_checked, root0Node7Step1Chunk1_1_checked, root0Node7Step1Chunk1_2_checked, root0Node7Step1Chunk1_3_checked, root0Node7Step1Chunk1_4_checked, root0Node7Step1Chunk1_5_checked, root0Node7Step1Chunk2_0_checked, root0Node7Step1Chunk2_1_checked, root0Node7Step1Chunk2_2_checked, root0Node7Step1Chunk2_3_checked, root0Node7Step1Chunk2_4_checked, root0Node7Step1Chunk2_5_checked, root0Node7Step1Chunk3_0_checked, root0Node7Step1Chunk3_1_checked, root0Node7Step1Chunk3_2_checked, root0Node7Step1Chunk3_3_checked, root0Node7Step1Chunk3_4_checked, root0Node7Step1Chunk3_5_checked, root0Node7Step1Chunk4_0_checked, root0Node7Step1Chunk4_1_checked, root0Node7Step1Chunk4_2_checked, root0Node7Step1Chunk4_3_checked, root0Node7Step1Chunk4_4_checked, root0Node7Step1Chunk4_5_checked, root0Node7Step1Chunk5_0_checked, root0Node7Step1Chunk5_1_checked, root0Node7Step1Chunk5_2_checked, root0Node7Step1Chunk5_3_checked, root0Node7Step1Chunk5_4_checked, root0Node7Step1Chunk5_5_checked, root0Node7Step1Chunk6_0_checked, root0Node7Step1Chunk6_1_checked, root0Node7Step1Chunk6_2_checked, root0Node7Step1Chunk6_3_checked, root0Node7Step1Chunk6_4_checked, root0Node7Step1Chunk6_5_checked, root0Node7Step1Chunk7_0_checked, root0Node7Step1Chunk7_1_checked, root0Node7Step1Chunk7_2_checked, root0Node7Step1Chunk7_3_checked, root0Node7Step1Chunk7_4_checked, root0Node7Step1Chunk7_5_checked, root0Node7Step1Chunk8_0_checked, root0Node7Step1Chunk8_1_checked, root0Node7Step1Chunk8_2_checked, root0Node7Step1Chunk8_3_checked, root0Node7Step1Chunk8_4_checked, root0Node7Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node7Step1_checked :
    checkReplacement table54 root0Node7Domains0 root0Node7Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node7Domains0 root0Node7Domains1
    root0Node7Domains0Fast root0Node7Domains1Fast
    root0Node7Domains0_fast_eq root0Node7Domains1_fast_eq
    root0Node7Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
