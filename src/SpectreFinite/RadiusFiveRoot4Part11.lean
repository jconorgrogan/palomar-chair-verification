module

public import SpectreFinite.RadiusFiveRoot4Part10
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable55
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node27Domains0 : Domains 91 State := restrict root4Node26Domains2 39 (4,1)
def root4Node27Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(3,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(2,3)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(6,4)]
  | 44 => some [(1,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3),(8,3)]
  | 50 => some [(5,2),(5,5)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(1,4),(6,4)]
  | 60 => some [(0,5),(1,2)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(4,2)]
  | 64 => some [(5,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3),(6,0)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2),(8,2)]
  | 78 => some [(0,3)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,1),(6,4)]
  | 84 => some [(1,2),(6,2)]
  | 85 => some [(1,3),(3,3),(5,3)]
  | 86 => some [(5,2),(5,5),(8,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root4Node27Domains0_fast_eq : root4Node27Domains0 = expandDomains root4Node27Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node27Domains0 v = expandDomains root4Node27Domains0Fast v from by decide) v
def root4Node27Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(8,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(3,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(2,3)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(4,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(6,4)]
  | 44 => [(1,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3)]
  | 50 => [(5,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(0,3)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(8,0)]
  | 62 => [(7,3)]
  | 63 => [(4,2)]
  | 64 => [(5,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(6,4)]
  | 71 => [(1,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3),(6,3)]
  | 74 => [(7,2),(8,2)]
  | 75 => [(4,0),(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(0,3)]
  | 79 => [(4,1),(8,1)]
  | 80 => [(0,2),(6,5)]
  | 81 => [(0,4),(1,1)]
  | 82 => [(5,1),(5,4)]
  | 83 => [(0,1),(6,4)]
  | 84 => [(1,2),(6,2)]
  | 85 => [(1,3),(3,3),(5,3)]
  | 86 => [(5,2),(5,5),(8,5)]
  | 87 => [(7,0),(8,0)]
  | 88 => [(4,3),(8,3)]
  | 89 => [(3,5),(5,5),(7,5)]
  | _ => [(0,3),(1,0)]
def root4Node27Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(3,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(2,3)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(6,4)]
  | 44 => some [(1,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(5,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(4,2)]
  | 64 => some [(5,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(0,3)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,1),(6,4)]
  | 84 => some [(1,2),(6,2)]
  | 85 => some [(1,3),(3,3),(5,3)]
  | 86 => some [(5,2),(5,5),(8,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root4Node27Domains1_fast_eq : root4Node27Domains1 = expandDomains root4Node27Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node27Domains1 v = expandDomains root4Node27Domains1Fast v from by decide) v
theorem root4Node27Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Narrowing_checked :
    checkNarrowing table36 root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root4Node27Domains0 root4Node27Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node27Step1Chunk0_0_checked, root4Node27Step1Chunk0_1_checked, root4Node27Step1Chunk0_2_checked, root4Node27Step1Chunk0_3_checked, root4Node27Step1Chunk0_4_checked, root4Node27Step1Chunk0_5_checked, root4Node27Step1Chunk1_0_checked, root4Node27Step1Chunk1_1_checked, root4Node27Step1Chunk1_2_checked, root4Node27Step1Chunk1_3_checked, root4Node27Step1Chunk1_4_checked, root4Node27Step1Chunk1_5_checked, root4Node27Step1Chunk2_0_checked, root4Node27Step1Chunk2_1_checked, root4Node27Step1Chunk2_2_checked, root4Node27Step1Chunk2_3_checked, root4Node27Step1Chunk2_4_checked, root4Node27Step1Chunk2_5_checked, root4Node27Step1Chunk3_0_checked, root4Node27Step1Chunk3_1_checked, root4Node27Step1Chunk3_2_checked, root4Node27Step1Chunk3_3_checked, root4Node27Step1Chunk3_4_checked, root4Node27Step1Chunk3_5_checked, root4Node27Step1Chunk4_0_checked, root4Node27Step1Chunk4_1_checked, root4Node27Step1Chunk4_2_checked, root4Node27Step1Chunk4_3_checked, root4Node27Step1Chunk4_4_checked, root4Node27Step1Chunk4_5_checked, root4Node27Step1Chunk5_0_checked, root4Node27Step1Chunk5_1_checked, root4Node27Step1Chunk5_2_checked, root4Node27Step1Chunk5_3_checked, root4Node27Step1Chunk5_4_checked, root4Node27Step1Chunk5_5_checked, root4Node27Step1Chunk6_0_checked, root4Node27Step1Chunk6_1_checked, root4Node27Step1Chunk6_2_checked, root4Node27Step1Chunk6_3_checked, root4Node27Step1Chunk6_4_checked, root4Node27Step1Chunk6_5_checked, root4Node27Step1Chunk7_0_checked, root4Node27Step1Chunk7_1_checked, root4Node27Step1Chunk7_2_checked, root4Node27Step1Chunk7_3_checked, root4Node27Step1Chunk7_4_checked, root4Node27Step1Chunk7_5_checked, root4Node27Step1Chunk8_0_checked, root4Node27Step1Chunk8_1_checked, root4Node27Step1Chunk8_2_checked, root4Node27Step1Chunk8_3_checked, root4Node27Step1Chunk8_4_checked, root4Node27Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node27Step1_checked :
    checkReplacement table36 root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq
    root4Node27Step1Narrowing_checked (by decide)
def root4Node28Domains0 : Domains 91 State := restrict root4Node27Domains1 73 (1,3)
def root4Node28Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(3,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(2,3)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(6,4)]
  | 44 => some [(1,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(5,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(4,2)]
  | 64 => some [(5,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(0,3)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,1),(6,4)]
  | 84 => some [(1,2),(6,2)]
  | 85 => some [(1,3),(3,3),(5,3)]
  | 86 => some [(5,2),(5,5),(8,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root4Node28Domains0_fast_eq : root4Node28Domains0 = expandDomains root4Node28Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node28Domains0 v = expandDomains root4Node28Domains0Fast v from by decide) v
def root4Node28Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(8,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(3,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(2,3)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(4,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(6,4)]
  | 44 => [(1,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3)]
  | 50 => [(5,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(0,3)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(8,0)]
  | 62 => [(7,3)]
  | 63 => [(4,2)]
  | 64 => [(5,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(6,4)]
  | 71 => [(1,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(0,3)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(5,3)]
  | 86 => [(5,5),(8,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(3,5),(7,5)]
  | _ => [(0,3)]
def root4Node28Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(3,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(2,3)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(6,4)]
  | 44 => some [(1,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(5,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(4,2)]
  | 64 => some [(5,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(0,3)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(5,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5),(7,5)]
  | _ => some [(0,3)]
theorem root4Node28Domains1_fast_eq : root4Node28Domains1 = expandDomains root4Node28Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node28Domains1 v = expandDomains root4Node28Domains1Fast v from by decide) v
theorem root4Node28Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Narrowing_checked :
    checkNarrowing table65 root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root4Node28Domains0 root4Node28Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node28Step1Chunk0_0_checked, root4Node28Step1Chunk0_1_checked, root4Node28Step1Chunk0_2_checked, root4Node28Step1Chunk0_3_checked, root4Node28Step1Chunk0_4_checked, root4Node28Step1Chunk0_5_checked, root4Node28Step1Chunk1_0_checked, root4Node28Step1Chunk1_1_checked, root4Node28Step1Chunk1_2_checked, root4Node28Step1Chunk1_3_checked, root4Node28Step1Chunk1_4_checked, root4Node28Step1Chunk1_5_checked, root4Node28Step1Chunk2_0_checked, root4Node28Step1Chunk2_1_checked, root4Node28Step1Chunk2_2_checked, root4Node28Step1Chunk2_3_checked, root4Node28Step1Chunk2_4_checked, root4Node28Step1Chunk2_5_checked, root4Node28Step1Chunk3_0_checked, root4Node28Step1Chunk3_1_checked, root4Node28Step1Chunk3_2_checked, root4Node28Step1Chunk3_3_checked, root4Node28Step1Chunk3_4_checked, root4Node28Step1Chunk3_5_checked, root4Node28Step1Chunk4_0_checked, root4Node28Step1Chunk4_1_checked, root4Node28Step1Chunk4_2_checked, root4Node28Step1Chunk4_3_checked, root4Node28Step1Chunk4_4_checked, root4Node28Step1Chunk4_5_checked, root4Node28Step1Chunk5_0_checked, root4Node28Step1Chunk5_1_checked, root4Node28Step1Chunk5_2_checked, root4Node28Step1Chunk5_3_checked, root4Node28Step1Chunk5_4_checked, root4Node28Step1Chunk5_5_checked, root4Node28Step1Chunk6_0_checked, root4Node28Step1Chunk6_1_checked, root4Node28Step1Chunk6_2_checked, root4Node28Step1Chunk6_3_checked, root4Node28Step1Chunk6_4_checked, root4Node28Step1Chunk6_5_checked, root4Node28Step1Chunk7_0_checked, root4Node28Step1Chunk7_1_checked, root4Node28Step1Chunk7_2_checked, root4Node28Step1Chunk7_3_checked, root4Node28Step1Chunk7_4_checked, root4Node28Step1Chunk7_5_checked, root4Node28Step1Chunk8_0_checked, root4Node28Step1Chunk8_1_checked, root4Node28Step1Chunk8_2_checked, root4Node28Step1Chunk8_3_checked, root4Node28Step1Chunk8_4_checked, root4Node28Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node28Step1_checked :
    checkReplacement table65 root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq
    root4Node28Step1Narrowing_checked (by decide)
def root4Node29Domains0 : Domains 91 State := restrict root4Node28Domains1 86 (5,5)
def root4Node29Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(3,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(2,3)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(6,4)]
  | 44 => some [(1,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(5,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(4,2)]
  | 64 => some [(5,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(0,3)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(5,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5),(7,5)]
  | _ => some [(0,3)]
theorem root4Node29Domains0_fast_eq : root4Node29Domains0 = expandDomains root4Node29Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node29Domains0 v = expandDomains root4Node29Domains0Fast v from by decide) v
def root4Node29Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(8,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(3,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(2,3)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(4,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(6,4)]
  | 44 => [(1,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3)]
  | 50 => [(5,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(0,3)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(8,0)]
  | 62 => [(7,3)]
  | 63 => [(4,2)]
  | 64 => [(5,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(6,4)]
  | 71 => [(1,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(0,3)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(5,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(3,5)]
  | _ => [(0,3)]
def root4Node29Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(3,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(2,3)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(6,4)]
  | 44 => some [(1,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(5,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(4,2)]
  | 64 => some [(5,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(0,3)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(5,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5)]
  | _ => some [(0,3)]
theorem root4Node29Domains1_fast_eq : root4Node29Domains1 = expandDomains root4Node29Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node29Domains1 v = expandDomains root4Node29Domains1Fast v from by decide) v
theorem root4Node29Step1Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Narrowing_checked :
    checkNarrowing table55 root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root4Node29Domains0 root4Node29Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node29Step1Chunk0_0_checked, root4Node29Step1Chunk0_1_checked, root4Node29Step1Chunk0_2_checked, root4Node29Step1Chunk0_3_checked, root4Node29Step1Chunk0_4_checked, root4Node29Step1Chunk0_5_checked, root4Node29Step1Chunk1_0_checked, root4Node29Step1Chunk1_1_checked, root4Node29Step1Chunk1_2_checked, root4Node29Step1Chunk1_3_checked, root4Node29Step1Chunk1_4_checked, root4Node29Step1Chunk1_5_checked, root4Node29Step1Chunk2_0_checked, root4Node29Step1Chunk2_1_checked, root4Node29Step1Chunk2_2_checked, root4Node29Step1Chunk2_3_checked, root4Node29Step1Chunk2_4_checked, root4Node29Step1Chunk2_5_checked, root4Node29Step1Chunk3_0_checked, root4Node29Step1Chunk3_1_checked, root4Node29Step1Chunk3_2_checked, root4Node29Step1Chunk3_3_checked, root4Node29Step1Chunk3_4_checked, root4Node29Step1Chunk3_5_checked, root4Node29Step1Chunk4_0_checked, root4Node29Step1Chunk4_1_checked, root4Node29Step1Chunk4_2_checked, root4Node29Step1Chunk4_3_checked, root4Node29Step1Chunk4_4_checked, root4Node29Step1Chunk4_5_checked, root4Node29Step1Chunk5_0_checked, root4Node29Step1Chunk5_1_checked, root4Node29Step1Chunk5_2_checked, root4Node29Step1Chunk5_3_checked, root4Node29Step1Chunk5_4_checked, root4Node29Step1Chunk5_5_checked, root4Node29Step1Chunk6_0_checked, root4Node29Step1Chunk6_1_checked, root4Node29Step1Chunk6_2_checked, root4Node29Step1Chunk6_3_checked, root4Node29Step1Chunk6_4_checked, root4Node29Step1Chunk6_5_checked, root4Node29Step1Chunk7_0_checked, root4Node29Step1Chunk7_1_checked, root4Node29Step1Chunk7_2_checked, root4Node29Step1Chunk7_3_checked, root4Node29Step1Chunk7_4_checked, root4Node29Step1Chunk7_5_checked, root4Node29Step1Chunk8_0_checked, root4Node29Step1Chunk8_1_checked, root4Node29Step1Chunk8_2_checked, root4Node29Step1Chunk8_3_checked, root4Node29Step1Chunk8_4_checked, root4Node29Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node29Step1_checked :
    checkReplacement table55 root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq
    root4Node29Step1Narrowing_checked (by decide)
theorem root4Node29Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node29Domains1 (.output 12) = true := by decide
def root4Node30Domains0 : Domains 91 State := restrict root4Node28Domains1 86 (8,5)
def root4Node30Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(3,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(2,3)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(6,4)]
  | 44 => some [(1,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(5,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(4,2)]
  | 64 => some [(5,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(0,3)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(5,3)]
  | 86 => some [(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5),(7,5)]
  | _ => some [(0,3)]
theorem root4Node30Domains0_fast_eq : root4Node30Domains0 = expandDomains root4Node30Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node30Domains0 v = expandDomains root4Node30Domains0Fast v from by decide) v
def root4Node30Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(4,3)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(8,1)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(3,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(7,0)]
  | 33 => [(2,3)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(4,1)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(6,4)]
  | 44 => [(1,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3)]
  | 50 => [(5,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(7,5)]
  | 54 => [(0,3)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(8,0)]
  | 62 => [(7,3)]
  | 63 => [(4,2)]
  | 64 => [(5,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(6,4)]
  | 71 => [(1,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(0,3)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(5,3)]
  | 86 => [(8,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(7,5)]
  | _ => [(0,3)]
def root4Node30Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(4,3)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(8,1)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(3,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(7,0)]
  | 33 => some [(2,3)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(4,1)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(6,4)]
  | 44 => some [(1,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(5,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(8,0)]
  | 62 => some [(7,3)]
  | 63 => some [(4,2)]
  | 64 => some [(5,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(6,4)]
  | 71 => some [(1,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(0,3)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(5,3)]
  | 86 => some [(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root4Node30Domains1_fast_eq : root4Node30Domains1 = expandDomains root4Node30Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node30Domains1 v = expandDomains root4Node30Domains1Fast v from by decide) v
theorem root4Node30Step1Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq (by decide)
theorem root4Node30Step1Narrowing_checked :
    checkNarrowing table55 root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root4Node30Domains0 root4Node30Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node30Step1Chunk0_0_checked, root4Node30Step1Chunk0_1_checked, root4Node30Step1Chunk0_2_checked, root4Node30Step1Chunk0_3_checked, root4Node30Step1Chunk0_4_checked, root4Node30Step1Chunk0_5_checked, root4Node30Step1Chunk1_0_checked, root4Node30Step1Chunk1_1_checked, root4Node30Step1Chunk1_2_checked, root4Node30Step1Chunk1_3_checked, root4Node30Step1Chunk1_4_checked, root4Node30Step1Chunk1_5_checked, root4Node30Step1Chunk2_0_checked, root4Node30Step1Chunk2_1_checked, root4Node30Step1Chunk2_2_checked, root4Node30Step1Chunk2_3_checked, root4Node30Step1Chunk2_4_checked, root4Node30Step1Chunk2_5_checked, root4Node30Step1Chunk3_0_checked, root4Node30Step1Chunk3_1_checked, root4Node30Step1Chunk3_2_checked, root4Node30Step1Chunk3_3_checked, root4Node30Step1Chunk3_4_checked, root4Node30Step1Chunk3_5_checked, root4Node30Step1Chunk4_0_checked, root4Node30Step1Chunk4_1_checked, root4Node30Step1Chunk4_2_checked, root4Node30Step1Chunk4_3_checked, root4Node30Step1Chunk4_4_checked, root4Node30Step1Chunk4_5_checked, root4Node30Step1Chunk5_0_checked, root4Node30Step1Chunk5_1_checked, root4Node30Step1Chunk5_2_checked, root4Node30Step1Chunk5_3_checked, root4Node30Step1Chunk5_4_checked, root4Node30Step1Chunk5_5_checked, root4Node30Step1Chunk6_0_checked, root4Node30Step1Chunk6_1_checked, root4Node30Step1Chunk6_2_checked, root4Node30Step1Chunk6_3_checked, root4Node30Step1Chunk6_4_checked, root4Node30Step1Chunk6_5_checked, root4Node30Step1Chunk7_0_checked, root4Node30Step1Chunk7_1_checked, root4Node30Step1Chunk7_2_checked, root4Node30Step1Chunk7_3_checked, root4Node30Step1Chunk7_4_checked, root4Node30Step1Chunk7_5_checked, root4Node30Step1Chunk8_0_checked, root4Node30Step1Chunk8_1_checked, root4Node30Step1Chunk8_2_checked, root4Node30Step1Chunk8_3_checked, root4Node30Step1Chunk8_4_checked, root4Node30Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node30Step1_checked :
    checkReplacement table55 root4Node30Domains0 root4Node30Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node30Domains0 root4Node30Domains1
    root4Node30Domains0Fast root4Node30Domains1Fast
    root4Node30Domains0_fast_eq root4Node30Domains1_fast_eq
    root4Node30Step1Narrowing_checked (by decide)
theorem root4Node30Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node30Domains1 (.output 13) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
