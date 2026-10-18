module

public import SpectreFinite.RadiusFiveRoot4Part7
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable55
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node16Domains0 : Domains 91 State := restrict root4Node15Domains1 50 (4,2)
def root4Node16Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(7,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(4,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3),(6,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,1),(6,4)]
  | 84 => some [(1,2),(6,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root4Node16Domains0_fast_eq : root4Node16Domains0 = expandDomains root4Node16Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node16Domains0 v = expandDomains root4Node16Domains0Fast v from by decide) v
def root4Node17Domains0 : Domains 91 State := restrict root4Node16Domains0 73 (1,3)
def root4Node17Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(7,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(4,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(7,2),(8,2)]
  | 75 => some [(4,0),(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(4,1),(8,1)]
  | 80 => some [(0,2),(6,5)]
  | 81 => some [(0,4),(1,1)]
  | 82 => some [(5,1),(5,4)]
  | 83 => some [(0,1),(6,4)]
  | 84 => some [(1,2),(6,2)]
  | 85 => some [(7,3),(8,3)]
  | 86 => some [(5,2),(5,5),(8,5)]
  | 87 => some [(7,0),(8,0)]
  | 88 => some [(4,3),(8,3)]
  | 89 => some [(3,5),(5,5),(7,5)]
  | _ => some [(0,3),(1,0)]
theorem root4Node17Domains0_fast_eq : root4Node17Domains0 = expandDomains root4Node17Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node17Domains0 v = expandDomains root4Node17Domains0Fast v from by decide) v
def root4Node17Domains1 (v : Fin 91) : List State :=
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
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(3,0)]
  | 33 => [(2,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(7,5)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3)]
  | 50 => [(4,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5),(8,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(3,5),(7,5)]
  | _ => [(0,3)]
def root4Node17Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(7,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(4,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5),(7,5)]
  | _ => some [(0,3)]
theorem root4Node17Domains1_fast_eq : root4Node17Domains1 = expandDomains root4Node17Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node17Domains1 v = expandDomains root4Node17Domains1Fast v from by decide) v
theorem root4Node17Step1Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Narrowing_checked :
    checkNarrowing table65 root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root4Node17Domains0 root4Node17Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node17Step1Chunk0_0_checked, root4Node17Step1Chunk0_1_checked, root4Node17Step1Chunk0_2_checked, root4Node17Step1Chunk0_3_checked, root4Node17Step1Chunk0_4_checked, root4Node17Step1Chunk0_5_checked, root4Node17Step1Chunk1_0_checked, root4Node17Step1Chunk1_1_checked, root4Node17Step1Chunk1_2_checked, root4Node17Step1Chunk1_3_checked, root4Node17Step1Chunk1_4_checked, root4Node17Step1Chunk1_5_checked, root4Node17Step1Chunk2_0_checked, root4Node17Step1Chunk2_1_checked, root4Node17Step1Chunk2_2_checked, root4Node17Step1Chunk2_3_checked, root4Node17Step1Chunk2_4_checked, root4Node17Step1Chunk2_5_checked, root4Node17Step1Chunk3_0_checked, root4Node17Step1Chunk3_1_checked, root4Node17Step1Chunk3_2_checked, root4Node17Step1Chunk3_3_checked, root4Node17Step1Chunk3_4_checked, root4Node17Step1Chunk3_5_checked, root4Node17Step1Chunk4_0_checked, root4Node17Step1Chunk4_1_checked, root4Node17Step1Chunk4_2_checked, root4Node17Step1Chunk4_3_checked, root4Node17Step1Chunk4_4_checked, root4Node17Step1Chunk4_5_checked, root4Node17Step1Chunk5_0_checked, root4Node17Step1Chunk5_1_checked, root4Node17Step1Chunk5_2_checked, root4Node17Step1Chunk5_3_checked, root4Node17Step1Chunk5_4_checked, root4Node17Step1Chunk5_5_checked, root4Node17Step1Chunk6_0_checked, root4Node17Step1Chunk6_1_checked, root4Node17Step1Chunk6_2_checked, root4Node17Step1Chunk6_3_checked, root4Node17Step1Chunk6_4_checked, root4Node17Step1Chunk6_5_checked, root4Node17Step1Chunk7_0_checked, root4Node17Step1Chunk7_1_checked, root4Node17Step1Chunk7_2_checked, root4Node17Step1Chunk7_3_checked, root4Node17Step1Chunk7_4_checked, root4Node17Step1Chunk7_5_checked, root4Node17Step1Chunk8_0_checked, root4Node17Step1Chunk8_1_checked, root4Node17Step1Chunk8_2_checked, root4Node17Step1Chunk8_3_checked, root4Node17Step1Chunk8_4_checked, root4Node17Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node17Step1_checked :
    checkReplacement table65 root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq
    root4Node17Step1Narrowing_checked (by decide)
def root4Node18Domains0 : Domains 91 State := restrict root4Node17Domains1 86 (5,5)
def root4Node18Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(7,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(4,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5),(7,5)]
  | _ => some [(0,3)]
theorem root4Node18Domains0_fast_eq : root4Node18Domains0 = expandDomains root4Node18Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node18Domains0 v = expandDomains root4Node18Domains0Fast v from by decide) v
def root4Node18Domains1 (v : Fin 91) : List State :=
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
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(3,0)]
  | 33 => [(2,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(7,5)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3)]
  | 50 => [(4,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(3,5)]
  | _ => [(0,3)]
def root4Node18Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(7,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(4,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5)]
  | _ => some [(0,3)]
theorem root4Node18Domains1_fast_eq : root4Node18Domains1 = expandDomains root4Node18Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node18Domains1 v = expandDomains root4Node18Domains1Fast v from by decide) v
theorem root4Node18Step1Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Narrowing_checked :
    checkNarrowing table55 root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root4Node18Domains0 root4Node18Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node18Step1Chunk0_0_checked, root4Node18Step1Chunk0_1_checked, root4Node18Step1Chunk0_2_checked, root4Node18Step1Chunk0_3_checked, root4Node18Step1Chunk0_4_checked, root4Node18Step1Chunk0_5_checked, root4Node18Step1Chunk1_0_checked, root4Node18Step1Chunk1_1_checked, root4Node18Step1Chunk1_2_checked, root4Node18Step1Chunk1_3_checked, root4Node18Step1Chunk1_4_checked, root4Node18Step1Chunk1_5_checked, root4Node18Step1Chunk2_0_checked, root4Node18Step1Chunk2_1_checked, root4Node18Step1Chunk2_2_checked, root4Node18Step1Chunk2_3_checked, root4Node18Step1Chunk2_4_checked, root4Node18Step1Chunk2_5_checked, root4Node18Step1Chunk3_0_checked, root4Node18Step1Chunk3_1_checked, root4Node18Step1Chunk3_2_checked, root4Node18Step1Chunk3_3_checked, root4Node18Step1Chunk3_4_checked, root4Node18Step1Chunk3_5_checked, root4Node18Step1Chunk4_0_checked, root4Node18Step1Chunk4_1_checked, root4Node18Step1Chunk4_2_checked, root4Node18Step1Chunk4_3_checked, root4Node18Step1Chunk4_4_checked, root4Node18Step1Chunk4_5_checked, root4Node18Step1Chunk5_0_checked, root4Node18Step1Chunk5_1_checked, root4Node18Step1Chunk5_2_checked, root4Node18Step1Chunk5_3_checked, root4Node18Step1Chunk5_4_checked, root4Node18Step1Chunk5_5_checked, root4Node18Step1Chunk6_0_checked, root4Node18Step1Chunk6_1_checked, root4Node18Step1Chunk6_2_checked, root4Node18Step1Chunk6_3_checked, root4Node18Step1Chunk6_4_checked, root4Node18Step1Chunk6_5_checked, root4Node18Step1Chunk7_0_checked, root4Node18Step1Chunk7_1_checked, root4Node18Step1Chunk7_2_checked, root4Node18Step1Chunk7_3_checked, root4Node18Step1Chunk7_4_checked, root4Node18Step1Chunk7_5_checked, root4Node18Step1Chunk8_0_checked, root4Node18Step1Chunk8_1_checked, root4Node18Step1Chunk8_2_checked, root4Node18Step1Chunk8_3_checked, root4Node18Step1Chunk8_4_checked, root4Node18Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node18Step1_checked :
    checkReplacement table55 root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq
    root4Node18Step1Narrowing_checked (by decide)
theorem root4Node18Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node18Domains1 (.output 6) = true := by decide
def root4Node19Domains0 : Domains 91 State := restrict root4Node17Domains1 86 (8,5)
def root4Node19Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(7,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(4,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(3,5),(7,5)]
  | _ => some [(0,3)]
theorem root4Node19Domains0_fast_eq : root4Node19Domains0 = expandDomains root4Node19Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node19Domains0 v = expandDomains root4Node19Domains0Fast v from by decide) v
def root4Node19Domains1 (v : Fin 91) : List State :=
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
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(5,5)]
  | 21 => [(8,1)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4)]
  | 28 => [(0,5)]
  | 29 => [(4,4)]
  | 30 => [(8,3)]
  | 31 => [(5,5)]
  | 32 => [(3,0)]
  | 33 => [(2,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(6,0)]
  | 38 => [(7,1)]
  | 39 => [(7,5)]
  | 40 => [(1,4)]
  | 41 => [(0,5)]
  | 42 => [(4,4)]
  | 43 => [(0,0)]
  | 44 => [(7,2)]
  | 45 => [(4,0)]
  | 46 => [(7,3)]
  | 47 => [(8,2)]
  | 48 => [(8,0)]
  | 49 => [(7,3)]
  | 50 => [(4,2)]
  | 51 => [(6,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1)]
  | 56 => [(0,1)]
  | 57 => [(6,2)]
  | 58 => [(8,4)]
  | 59 => [(6,4)]
  | 60 => [(1,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(7,0)]
  | 64 => [(8,3)]
  | 65 => [(8,5)]
  | 66 => [(1,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(0,3)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(7,4)]
  | 73 => [(1,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(4,2)]
  | 78 => [(6,1)]
  | 79 => [(8,1)]
  | 80 => [(6,5)]
  | 81 => [(0,4)]
  | 82 => [(5,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(8,3)]
  | 86 => [(8,5)]
  | 87 => [(7,0)]
  | 88 => [(4,3)]
  | 89 => [(7,5)]
  | _ => [(0,3)]
def root4Node19Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(5,5)]
  | 21 => some [(8,1)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4)]
  | 28 => some [(0,5)]
  | 29 => some [(4,4)]
  | 30 => some [(8,3)]
  | 31 => some [(5,5)]
  | 32 => some [(3,0)]
  | 33 => some [(2,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(6,0)]
  | 38 => some [(7,1)]
  | 39 => some [(7,5)]
  | 40 => some [(1,4)]
  | 41 => some [(0,5)]
  | 42 => some [(4,4)]
  | 43 => some [(0,0)]
  | 44 => some [(7,2)]
  | 45 => some [(4,0)]
  | 46 => some [(7,3)]
  | 47 => some [(8,2)]
  | 48 => some [(8,0)]
  | 49 => some [(7,3)]
  | 50 => some [(4,2)]
  | 51 => some [(6,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1)]
  | 56 => some [(0,1)]
  | 57 => some [(6,2)]
  | 58 => some [(8,4)]
  | 59 => some [(6,4)]
  | 60 => some [(1,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(7,0)]
  | 64 => some [(8,3)]
  | 65 => some [(8,5)]
  | 66 => some [(1,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(0,3)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(7,4)]
  | 73 => some [(1,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(4,2)]
  | 78 => some [(6,1)]
  | 79 => some [(8,1)]
  | 80 => some [(6,5)]
  | 81 => some [(0,4)]
  | 82 => some [(5,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(7,0)]
  | 88 => some [(4,3)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root4Node19Domains1_fast_eq : root4Node19Domains1 = expandDomains root4Node19Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root4Node19Domains1 v = expandDomains root4Node19Domains1Fast v from by decide) v
theorem root4Node19Step1Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Narrowing_checked :
    checkNarrowing table55 root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root4Node19Domains0 root4Node19Domains1 (by
      simp only [List.all_cons, List.all_nil, root4Node19Step1Chunk0_0_checked, root4Node19Step1Chunk0_1_checked, root4Node19Step1Chunk0_2_checked, root4Node19Step1Chunk0_3_checked, root4Node19Step1Chunk0_4_checked, root4Node19Step1Chunk0_5_checked, root4Node19Step1Chunk1_0_checked, root4Node19Step1Chunk1_1_checked, root4Node19Step1Chunk1_2_checked, root4Node19Step1Chunk1_3_checked, root4Node19Step1Chunk1_4_checked, root4Node19Step1Chunk1_5_checked, root4Node19Step1Chunk2_0_checked, root4Node19Step1Chunk2_1_checked, root4Node19Step1Chunk2_2_checked, root4Node19Step1Chunk2_3_checked, root4Node19Step1Chunk2_4_checked, root4Node19Step1Chunk2_5_checked, root4Node19Step1Chunk3_0_checked, root4Node19Step1Chunk3_1_checked, root4Node19Step1Chunk3_2_checked, root4Node19Step1Chunk3_3_checked, root4Node19Step1Chunk3_4_checked, root4Node19Step1Chunk3_5_checked, root4Node19Step1Chunk4_0_checked, root4Node19Step1Chunk4_1_checked, root4Node19Step1Chunk4_2_checked, root4Node19Step1Chunk4_3_checked, root4Node19Step1Chunk4_4_checked, root4Node19Step1Chunk4_5_checked, root4Node19Step1Chunk5_0_checked, root4Node19Step1Chunk5_1_checked, root4Node19Step1Chunk5_2_checked, root4Node19Step1Chunk5_3_checked, root4Node19Step1Chunk5_4_checked, root4Node19Step1Chunk5_5_checked, root4Node19Step1Chunk6_0_checked, root4Node19Step1Chunk6_1_checked, root4Node19Step1Chunk6_2_checked, root4Node19Step1Chunk6_3_checked, root4Node19Step1Chunk6_4_checked, root4Node19Step1Chunk6_5_checked, root4Node19Step1Chunk7_0_checked, root4Node19Step1Chunk7_1_checked, root4Node19Step1Chunk7_2_checked, root4Node19Step1Chunk7_3_checked, root4Node19Step1Chunk7_4_checked, root4Node19Step1Chunk7_5_checked, root4Node19Step1Chunk8_0_checked, root4Node19Step1Chunk8_1_checked, root4Node19Step1Chunk8_2_checked, root4Node19Step1Chunk8_3_checked, root4Node19Step1Chunk8_4_checked, root4Node19Step1Chunk8_5_checked, Bool.true_and])
theorem root4Node19Step1_checked :
    checkReplacement table55 root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq
    root4Node19Step1Narrowing_checked (by decide)
theorem root4Node19Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node19Domains1 (.output 7) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
