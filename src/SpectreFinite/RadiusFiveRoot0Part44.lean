module

public import SpectreFinite.RadiusFiveRoot0Part43
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable57

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node107Domains0 : Domains 91 State := restrict root0Node106Domains2 29 (1,4)
def root0Node107Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(2,2)]
  | 18 => some [(3,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(1,2),(3,2),(5,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(0,3),(6,0)]
  | 40 => some [(0,3),(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(4,2),(8,2)]
  | 50 => some [(5,0),(5,3),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(7,4),(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(2,1),(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2)]
  | 77 => some [(0,0),(4,0),(5,0),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 79 => some [(0,2),(1,5),(6,0)]
  | 80 => some [(1,1),(6,1),(7,1)]
  | 81 => some [(4,1),(7,5),(8,1)]
  | 82 => some [(0,2),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(5,1),(5,4)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => some [(2,0),(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,2)]
  | 89 => some [(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(8,3)]
theorem root0Node107Domains0_fast_eq : root0Node107Domains0 = expandDomains root0Node107Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node107Domains0 v = expandDomains root0Node107Domains0Fast v from by decide) v
def root0Node107Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(8,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(2,2)]
  | 18 => [(3,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,1)]
  | 27 => [(6,2)]
  | 28 => [(8,4)]
  | 29 => [(1,4)]
  | 30 => [(1,2),(3,2),(5,2)]
  | 31 => [(4,0),(8,0)]
  | 32 => [(7,3)]
  | 33 => [(5,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(0,3),(0,4),(6,1),(6,2)]
  | 41 => [(5,1),(5,4),(8,4)]
  | 42 => [(0,1),(6,4)]
  | 43 => [(1,2),(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0),(8,0)]
  | 51 => [(4,3),(5,3),(7,1),(8,3)]
  | 52 => [(7,5),(8,5)]
  | 53 => [(0,3),(1,0)]
  | 54 => [(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(1,3),(7,3)]
  | 62 => [(4,2),(8,2)]
  | 63 => [(5,0),(5,3)]
  | 64 => [(4,5),(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(0,4),(1,2),(6,2)]
  | 71 => [(1,4),(3,4),(5,4),(7,4)]
  | 72 => [(0,0),(6,3)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3),(6,3)]
  | 76 => [(7,2),(8,2)]
  | 77 => [(4,0),(5,0),(8,0)]
  | 78 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 79 => [(0,2),(1,5),(6,0)]
  | 80 => [(1,1),(6,1)]
  | 81 => [(4,1),(8,1)]
  | 82 => [(0,2),(6,5)]
  | 83 => [(0,4),(1,1)]
  | 84 => [(5,1),(5,4)]
  | 85 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => [(2,0),(4,0),(8,0)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5)]
  | 89 => [(7,0),(8,0)]
  | _ => [(4,3),(8,3)]
def root0Node107Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(2,2)]
  | 18 => some [(3,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(1,2),(3,2),(5,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(0,3),(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(6,3)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(5,0),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 79 => some [(0,2),(1,5),(6,0)]
  | 80 => some [(1,1),(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => some [(2,0),(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node107Domains1_fast_eq : root0Node107Domains1 = expandDomains root0Node107Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node107Domains1 v = expandDomains root0Node107Domains1Fast v from by decide) v
theorem root0Node107Step1Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq (by decide)
theorem root0Node107Step1Narrowing_checked :
    checkNarrowing table57 root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root0Node107Domains0 root0Node107Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node107Step1Chunk0_0_checked, root0Node107Step1Chunk0_1_checked, root0Node107Step1Chunk0_2_checked, root0Node107Step1Chunk0_3_checked, root0Node107Step1Chunk0_4_checked, root0Node107Step1Chunk0_5_checked, root0Node107Step1Chunk1_0_checked, root0Node107Step1Chunk1_1_checked, root0Node107Step1Chunk1_2_checked, root0Node107Step1Chunk1_3_checked, root0Node107Step1Chunk1_4_checked, root0Node107Step1Chunk1_5_checked, root0Node107Step1Chunk2_0_checked, root0Node107Step1Chunk2_1_checked, root0Node107Step1Chunk2_2_checked, root0Node107Step1Chunk2_3_checked, root0Node107Step1Chunk2_4_checked, root0Node107Step1Chunk2_5_checked, root0Node107Step1Chunk3_0_checked, root0Node107Step1Chunk3_1_checked, root0Node107Step1Chunk3_2_checked, root0Node107Step1Chunk3_3_checked, root0Node107Step1Chunk3_4_checked, root0Node107Step1Chunk3_5_checked, root0Node107Step1Chunk4_0_checked, root0Node107Step1Chunk4_1_checked, root0Node107Step1Chunk4_2_checked, root0Node107Step1Chunk4_3_checked, root0Node107Step1Chunk4_4_checked, root0Node107Step1Chunk4_5_checked, root0Node107Step1Chunk5_0_checked, root0Node107Step1Chunk5_1_checked, root0Node107Step1Chunk5_2_checked, root0Node107Step1Chunk5_3_checked, root0Node107Step1Chunk5_4_checked, root0Node107Step1Chunk5_5_checked, root0Node107Step1Chunk6_0_checked, root0Node107Step1Chunk6_1_checked, root0Node107Step1Chunk6_2_checked, root0Node107Step1Chunk6_3_checked, root0Node107Step1Chunk6_4_checked, root0Node107Step1Chunk6_5_checked, root0Node107Step1Chunk7_0_checked, root0Node107Step1Chunk7_1_checked, root0Node107Step1Chunk7_2_checked, root0Node107Step1Chunk7_3_checked, root0Node107Step1Chunk7_4_checked, root0Node107Step1Chunk7_5_checked, root0Node107Step1Chunk8_0_checked, root0Node107Step1Chunk8_1_checked, root0Node107Step1Chunk8_2_checked, root0Node107Step1Chunk8_3_checked, root0Node107Step1Chunk8_4_checked, root0Node107Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node107Step1_checked :
    checkReplacement table57 root0Node107Domains0 root0Node107Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node107Domains0 root0Node107Domains1
    root0Node107Domains0Fast root0Node107Domains1Fast
    root0Node107Domains0_fast_eq root0Node107Domains1_fast_eq
    root0Node107Step1Narrowing_checked (by decide)
def root0Node107Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(8,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(2,2)]
  | 18 => [(3,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,1)]
  | 27 => [(6,2)]
  | 28 => [(8,4)]
  | 29 => [(1,4)]
  | 30 => [(1,2),(3,2),(5,2)]
  | 31 => [(4,0),(8,0)]
  | 32 => [(7,3)]
  | 33 => [(5,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(0,3),(0,4),(6,1),(6,2)]
  | 41 => [(5,1),(5,4),(8,4)]
  | 42 => [(0,1),(6,4)]
  | 43 => [(1,2),(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0),(8,0)]
  | 51 => [(4,3),(5,3),(7,1),(8,3)]
  | 52 => [(7,5),(8,5)]
  | 53 => [(0,3),(1,0)]
  | 54 => [(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1)]
  | 58 => [(0,1)]
  | 59 => [(6,2)]
  | 60 => [(8,4)]
  | 61 => [(1,3),(7,3)]
  | 62 => [(4,2),(8,2)]
  | 63 => [(5,0),(5,3)]
  | 64 => [(4,5),(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(8,5)]
  | 68 => [(1,0)]
  | 69 => [(7,1)]
  | 70 => [(0,4),(1,2),(6,2)]
  | 71 => [(3,4),(5,4),(7,4)]
  | 72 => [(0,0),(6,3)]
  | 73 => [(7,2)]
  | 74 => [(7,4)]
  | 75 => [(1,3),(6,3)]
  | 76 => [(7,2),(8,2)]
  | 77 => [(4,0),(5,0),(8,0)]
  | 78 => [(2,1),(2,3),(4,1),(4,3)]
  | 79 => [(0,2),(1,5)]
  | 80 => [(1,1),(6,1)]
  | 81 => [(4,1),(8,1)]
  | 82 => [(0,2),(6,5)]
  | 83 => [(0,4),(1,1)]
  | 84 => [(5,1),(5,4)]
  | 85 => [(0,5),(1,2),(3,2),(5,2)]
  | 86 => [(2,0),(4,0),(8,0)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5)]
  | 89 => [(7,0),(8,0)]
  | _ => [(4,3),(8,3)]
def root0Node107Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(2,2)]
  | 18 => some [(3,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(1,2),(3,2),(5,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(0,3),(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(6,3)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(5,0),(8,0)]
  | 78 => some [(2,1),(2,3),(4,1),(4,3)]
  | 79 => some [(0,2),(1,5)]
  | 80 => some [(1,1),(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2)]
  | 86 => some [(2,0),(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node107Domains2_fast_eq : root0Node107Domains2 = expandDomains root0Node107Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node107Domains2 v = expandDomains root0Node107Domains2Fast v from by decide) v
theorem root0Node107Step2Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq (by decide)
theorem root0Node107Step2Narrowing_checked :
    checkNarrowing table51 root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root0Node107Domains1 root0Node107Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node107Step2Chunk0_0_checked, root0Node107Step2Chunk0_1_checked, root0Node107Step2Chunk0_2_checked, root0Node107Step2Chunk0_3_checked, root0Node107Step2Chunk0_4_checked, root0Node107Step2Chunk0_5_checked, root0Node107Step2Chunk1_0_checked, root0Node107Step2Chunk1_1_checked, root0Node107Step2Chunk1_2_checked, root0Node107Step2Chunk1_3_checked, root0Node107Step2Chunk1_4_checked, root0Node107Step2Chunk1_5_checked, root0Node107Step2Chunk2_0_checked, root0Node107Step2Chunk2_1_checked, root0Node107Step2Chunk2_2_checked, root0Node107Step2Chunk2_3_checked, root0Node107Step2Chunk2_4_checked, root0Node107Step2Chunk2_5_checked, root0Node107Step2Chunk3_0_checked, root0Node107Step2Chunk3_1_checked, root0Node107Step2Chunk3_2_checked, root0Node107Step2Chunk3_3_checked, root0Node107Step2Chunk3_4_checked, root0Node107Step2Chunk3_5_checked, root0Node107Step2Chunk4_0_checked, root0Node107Step2Chunk4_1_checked, root0Node107Step2Chunk4_2_checked, root0Node107Step2Chunk4_3_checked, root0Node107Step2Chunk4_4_checked, root0Node107Step2Chunk4_5_checked, root0Node107Step2Chunk5_0_checked, root0Node107Step2Chunk5_1_checked, root0Node107Step2Chunk5_2_checked, root0Node107Step2Chunk5_3_checked, root0Node107Step2Chunk5_4_checked, root0Node107Step2Chunk5_5_checked, root0Node107Step2Chunk6_0_checked, root0Node107Step2Chunk6_1_checked, root0Node107Step2Chunk6_2_checked, root0Node107Step2Chunk6_3_checked, root0Node107Step2Chunk6_4_checked, root0Node107Step2Chunk6_5_checked, root0Node107Step2Chunk7_0_checked, root0Node107Step2Chunk7_1_checked, root0Node107Step2Chunk7_2_checked, root0Node107Step2Chunk7_3_checked, root0Node107Step2Chunk7_4_checked, root0Node107Step2Chunk7_5_checked, root0Node107Step2Chunk8_0_checked, root0Node107Step2Chunk8_1_checked, root0Node107Step2Chunk8_2_checked, root0Node107Step2Chunk8_3_checked, root0Node107Step2Chunk8_4_checked, root0Node107Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node107Step2_checked :
    checkReplacement table51 root0Node107Domains1 root0Node107Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node107Domains1 root0Node107Domains2
    root0Node107Domains1Fast root0Node107Domains2Fast
    root0Node107Domains1_fast_eq root0Node107Domains2_fast_eq
    root0Node107Step2Narrowing_checked (by decide)
def root0Node108Domains0 : Domains 91 State := restrict root0Node107Domains2 31 (4,0)
def root0Node108Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(2,2)]
  | 18 => some [(3,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(1,2),(3,2),(5,2)]
  | 31 => some [(4,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(0,3),(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1)]
  | 58 => some [(0,1)]
  | 59 => some [(6,2)]
  | 60 => some [(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(8,5)]
  | 68 => some [(1,0)]
  | 69 => some [(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(6,3)]
  | 73 => some [(7,2)]
  | 74 => some [(7,4)]
  | 75 => some [(1,3),(6,3)]
  | 76 => some [(7,2),(8,2)]
  | 77 => some [(4,0),(5,0),(8,0)]
  | 78 => some [(2,1),(2,3),(4,1),(4,3)]
  | 79 => some [(0,2),(1,5)]
  | 80 => some [(1,1),(6,1)]
  | 81 => some [(4,1),(8,1)]
  | 82 => some [(0,2),(6,5)]
  | 83 => some [(0,4),(1,1)]
  | 84 => some [(5,1),(5,4)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2)]
  | 86 => some [(2,0),(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5)]
  | 89 => some [(7,0),(8,0)]
  | _ => some [(4,3),(8,3)]
theorem root0Node108Domains0_fast_eq : root0Node108Domains0 = expandDomains root0Node108Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node108Domains0 v = expandDomains root0Node108Domains0Fast v from by decide) v
def root0Node108Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(8,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(2,2)]
  | 18 => [(3,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,1)]
  | 27 => [(6,2)]
  | 28 => [(8,4)]
  | 29 => [(1,4)]
  | 30 => [(1,2),(3,2)]
  | 31 => [(4,0)]
  | 32 => [(7,3)]
  | 33 => [(5,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(0,3),(6,1)]
  | 41 => [(5,1)]
  | 42 => [(0,1)]
  | 43 => [(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(5,0),(8,0)]
  | 51 => [(5,3),(8,3)]
  | 52 => [(8,5)]
  | 53 => [(1,0)]
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
  | 77 => [(4,0),(5,0),(8,0)]
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
def root0Node108Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(2,2)]
  | 18 => some [(3,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(1,2),(3,2)]
  | 31 => some [(4,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(0,3),(6,1)]
  | 41 => some [(5,1)]
  | 42 => some [(0,1)]
  | 43 => some [(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(5,0),(8,0)]
  | 51 => some [(5,3),(8,3)]
  | 52 => some [(8,5)]
  | 53 => some [(1,0)]
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
  | 77 => some [(4,0),(5,0),(8,0)]
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
theorem root0Node108Domains1_fast_eq : root0Node108Domains1 = expandDomains root0Node108Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node108Domains1 v = expandDomains root0Node108Domains1Fast v from by decide) v
theorem root0Node108Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq (by decide)
theorem root0Node108Step1Narrowing_checked :
    checkNarrowing table54 root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root0Node108Domains0 root0Node108Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node108Step1Chunk0_0_checked, root0Node108Step1Chunk0_1_checked, root0Node108Step1Chunk0_2_checked, root0Node108Step1Chunk0_3_checked, root0Node108Step1Chunk0_4_checked, root0Node108Step1Chunk0_5_checked, root0Node108Step1Chunk1_0_checked, root0Node108Step1Chunk1_1_checked, root0Node108Step1Chunk1_2_checked, root0Node108Step1Chunk1_3_checked, root0Node108Step1Chunk1_4_checked, root0Node108Step1Chunk1_5_checked, root0Node108Step1Chunk2_0_checked, root0Node108Step1Chunk2_1_checked, root0Node108Step1Chunk2_2_checked, root0Node108Step1Chunk2_3_checked, root0Node108Step1Chunk2_4_checked, root0Node108Step1Chunk2_5_checked, root0Node108Step1Chunk3_0_checked, root0Node108Step1Chunk3_1_checked, root0Node108Step1Chunk3_2_checked, root0Node108Step1Chunk3_3_checked, root0Node108Step1Chunk3_4_checked, root0Node108Step1Chunk3_5_checked, root0Node108Step1Chunk4_0_checked, root0Node108Step1Chunk4_1_checked, root0Node108Step1Chunk4_2_checked, root0Node108Step1Chunk4_3_checked, root0Node108Step1Chunk4_4_checked, root0Node108Step1Chunk4_5_checked, root0Node108Step1Chunk5_0_checked, root0Node108Step1Chunk5_1_checked, root0Node108Step1Chunk5_2_checked, root0Node108Step1Chunk5_3_checked, root0Node108Step1Chunk5_4_checked, root0Node108Step1Chunk5_5_checked, root0Node108Step1Chunk6_0_checked, root0Node108Step1Chunk6_1_checked, root0Node108Step1Chunk6_2_checked, root0Node108Step1Chunk6_3_checked, root0Node108Step1Chunk6_4_checked, root0Node108Step1Chunk6_5_checked, root0Node108Step1Chunk7_0_checked, root0Node108Step1Chunk7_1_checked, root0Node108Step1Chunk7_2_checked, root0Node108Step1Chunk7_3_checked, root0Node108Step1Chunk7_4_checked, root0Node108Step1Chunk7_5_checked, root0Node108Step1Chunk8_0_checked, root0Node108Step1Chunk8_1_checked, root0Node108Step1Chunk8_2_checked, root0Node108Step1Chunk8_3_checked, root0Node108Step1Chunk8_4_checked, root0Node108Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node108Step1_checked :
    checkReplacement table54 root0Node108Domains0 root0Node108Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node108Domains0 root0Node108Domains1
    root0Node108Domains0Fast root0Node108Domains1Fast
    root0Node108Domains0_fast_eq root0Node108Domains1_fast_eq
    root0Node108Step1Narrowing_checked (by decide)
def root0Node108Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(8,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(7,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(6,3)]
  | 14 => [(7,2)]
  | 15 => [(7,4)]
  | 16 => [(6,3)]
  | 17 => [(2,2)]
  | 18 => [(3,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,1)]
  | 27 => [(6,2)]
  | 28 => [(8,4)]
  | 29 => [(1,4)]
  | 30 => [(1,2),(3,2)]
  | 31 => [(4,0)]
  | 32 => [(7,3)]
  | 33 => [(5,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(7,5)]
  | 39 => [(6,0)]
  | 40 => [(0,3),(6,1)]
  | 41 => [(5,1)]
  | 42 => [(0,1)]
  | 43 => [(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0)]
  | 48 => [(7,3)]
  | 49 => [(8,2)]
  | 50 => [(8,0)]
  | 51 => [(5,3),(8,3)]
  | 52 => [(8,5)]
  | 53 => [(1,0)]
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
def root0Node108Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(6,3)]
  | 14 => some [(7,2)]
  | 15 => some [(7,4)]
  | 16 => some [(6,3)]
  | 17 => some [(2,2)]
  | 18 => some [(3,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,1)]
  | 27 => some [(6,2)]
  | 28 => some [(8,4)]
  | 29 => some [(1,4)]
  | 30 => some [(1,2),(3,2)]
  | 31 => some [(4,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(6,0)]
  | 40 => some [(0,3),(6,1)]
  | 41 => some [(5,1)]
  | 42 => some [(0,1)]
  | 43 => some [(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0)]
  | 48 => some [(7,3)]
  | 49 => some [(8,2)]
  | 50 => some [(8,0)]
  | 51 => some [(5,3),(8,3)]
  | 52 => some [(8,5)]
  | 53 => some [(1,0)]
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
theorem root0Node108Domains2_fast_eq : root0Node108Domains2 = expandDomains root0Node108Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node108Domains2 v = expandDomains root0Node108Domains2Fast v from by decide) v
theorem root0Node108Step2Chunk0_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_0⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk0_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_1⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk0_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_2⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk0_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_3⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk0_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_4⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk0_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows0_5⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk1_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_0⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk1_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_1⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk1_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_2⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk1_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_3⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk1_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_4⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk1_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows1_5⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk2_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_0⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk2_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_1⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk2_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_2⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk2_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_3⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk2_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_4⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk2_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows2_5⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk3_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_0⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk3_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_1⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk3_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_2⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk3_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_3⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk3_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_4⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk3_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows3_5⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk4_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_0⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk4_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_1⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk4_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_2⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk4_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_3⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk4_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_4⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk4_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows4_5⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk5_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_0⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk5_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_1⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk5_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_2⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk5_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_3⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk5_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_4⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk5_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows5_5⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk6_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_0⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk6_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_1⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk6_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_2⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk6_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_3⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk6_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_4⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk6_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows6_5⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk7_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_0⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk7_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_1⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk7_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_2⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk7_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_3⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk7_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_4⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk7_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows7_5⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk8_0_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_0⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk8_1_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_1⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk8_2_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_2⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk8_3_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_3⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk8_4_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_4⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Chunk8_5_checked :
    checkNarrowing ⟨table57Scope, table57Rows8_5⟩
      root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq (by decide)
theorem root0Node108Step2Narrowing_checked :
    checkNarrowing table57 root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkNarrowing_flatten table57Scope [table57Rows0_0,table57Rows0_1,table57Rows0_2,table57Rows0_3,table57Rows0_4,table57Rows0_5,table57Rows1_0,table57Rows1_1,table57Rows1_2,table57Rows1_3,table57Rows1_4,table57Rows1_5,table57Rows2_0,table57Rows2_1,table57Rows2_2,table57Rows2_3,table57Rows2_4,table57Rows2_5,table57Rows3_0,table57Rows3_1,table57Rows3_2,table57Rows3_3,table57Rows3_4,table57Rows3_5,table57Rows4_0,table57Rows4_1,table57Rows4_2,table57Rows4_3,table57Rows4_4,table57Rows4_5,table57Rows5_0,table57Rows5_1,table57Rows5_2,table57Rows5_3,table57Rows5_4,table57Rows5_5,table57Rows6_0,table57Rows6_1,table57Rows6_2,table57Rows6_3,table57Rows6_4,table57Rows6_5,table57Rows7_0,table57Rows7_1,table57Rows7_2,table57Rows7_3,table57Rows7_4,table57Rows7_5,table57Rows8_0,table57Rows8_1,table57Rows8_2,table57Rows8_3,table57Rows8_4,table57Rows8_5]
    root0Node108Domains1 root0Node108Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node108Step2Chunk0_0_checked, root0Node108Step2Chunk0_1_checked, root0Node108Step2Chunk0_2_checked, root0Node108Step2Chunk0_3_checked, root0Node108Step2Chunk0_4_checked, root0Node108Step2Chunk0_5_checked, root0Node108Step2Chunk1_0_checked, root0Node108Step2Chunk1_1_checked, root0Node108Step2Chunk1_2_checked, root0Node108Step2Chunk1_3_checked, root0Node108Step2Chunk1_4_checked, root0Node108Step2Chunk1_5_checked, root0Node108Step2Chunk2_0_checked, root0Node108Step2Chunk2_1_checked, root0Node108Step2Chunk2_2_checked, root0Node108Step2Chunk2_3_checked, root0Node108Step2Chunk2_4_checked, root0Node108Step2Chunk2_5_checked, root0Node108Step2Chunk3_0_checked, root0Node108Step2Chunk3_1_checked, root0Node108Step2Chunk3_2_checked, root0Node108Step2Chunk3_3_checked, root0Node108Step2Chunk3_4_checked, root0Node108Step2Chunk3_5_checked, root0Node108Step2Chunk4_0_checked, root0Node108Step2Chunk4_1_checked, root0Node108Step2Chunk4_2_checked, root0Node108Step2Chunk4_3_checked, root0Node108Step2Chunk4_4_checked, root0Node108Step2Chunk4_5_checked, root0Node108Step2Chunk5_0_checked, root0Node108Step2Chunk5_1_checked, root0Node108Step2Chunk5_2_checked, root0Node108Step2Chunk5_3_checked, root0Node108Step2Chunk5_4_checked, root0Node108Step2Chunk5_5_checked, root0Node108Step2Chunk6_0_checked, root0Node108Step2Chunk6_1_checked, root0Node108Step2Chunk6_2_checked, root0Node108Step2Chunk6_3_checked, root0Node108Step2Chunk6_4_checked, root0Node108Step2Chunk6_5_checked, root0Node108Step2Chunk7_0_checked, root0Node108Step2Chunk7_1_checked, root0Node108Step2Chunk7_2_checked, root0Node108Step2Chunk7_3_checked, root0Node108Step2Chunk7_4_checked, root0Node108Step2Chunk7_5_checked, root0Node108Step2Chunk8_0_checked, root0Node108Step2Chunk8_1_checked, root0Node108Step2Chunk8_2_checked, root0Node108Step2Chunk8_3_checked, root0Node108Step2Chunk8_4_checked, root0Node108Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node108Step2_checked :
    checkReplacement table57 root0Node108Domains1 root0Node108Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node108Domains1 root0Node108Domains2
    root0Node108Domains1Fast root0Node108Domains2Fast
    root0Node108Domains1_fast_eq root0Node108Domains2_fast_eq
    root0Node108Step2Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
