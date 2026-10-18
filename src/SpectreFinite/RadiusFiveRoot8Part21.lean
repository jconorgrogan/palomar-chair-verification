module

public import SpectreFinite.RadiusFiveRoot8Part20
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable36
public import SpectreFinite.RadiusFiveTable55
public import SpectreFinite.RadiusFiveTable56
public import SpectreFinite.RadiusFiveTable6

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node52Domains0 : Domains 91 State := restrict root8Node48Domains2 31 (7,5)
def root8Node52Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(4,3)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(0,5),(6,3)]
  | 42 => some [(2,2),(2,4)]
  | 43 => some [(1,3),(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,2),(6,0)]
  | 52 => some [(1,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0),(7,4)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,5),(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1),(8,1)]
  | 80 => some [(0,1),(6,5)]
  | 81 => some [(0,4),(6,2)]
  | 82 => some [(1,4),(3,4),(7,4)]
  | 83 => some [(0,5),(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5)]
  | 89 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root8Node52Domains0_fast_eq : root8Node52Domains0 = expandDomains root8Node52Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node52Domains0 v = expandDomains root8Node52Domains0Fast v from by decide) v
def root8Node52Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(2,2)]
  | 30 => [(4,3)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(0,1)]
  | 40 => [(1,4),(7,4)]
  | 41 => [(6,3)]
  | 42 => [(2,2)]
  | 43 => [(3,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(0,2)]
  | 52 => [(1,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(4,4),(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(1,0)]
  | 88 => [(2,1)]
  | 89 => [(0,2)]
  | _ => [(1,1),(7,1)]
def root8Node52Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(4,3)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(6,3)]
  | 42 => some [(2,2)]
  | 43 => some [(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,2)]
  | 52 => some [(1,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(1,0)]
  | 88 => some [(2,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1),(7,1)]
theorem root8Node52Domains1_fast_eq : root8Node52Domains1 = expandDomains root8Node52Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node52Domains1 v = expandDomains root8Node52Domains1Fast v from by decide) v
theorem root8Node52Step1Chunk0_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk0_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk0_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk0_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk0_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk0_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows0_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk1_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows1_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk2_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows2_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk3_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows3_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk4_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows4_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk5_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows5_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk6_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows6_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk7_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows7_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_0_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_0⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_1_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_1⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_2_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_2⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_3_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_3⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_4_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_4⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Chunk8_5_checked :
    checkNarrowing ⟨table55Scope, table55Rows8_5⟩
      root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq (by decide)
theorem root8Node52Step1Narrowing_checked :
    checkNarrowing table55 root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkNarrowing_flatten table55Scope [table55Rows0_0,table55Rows0_1,table55Rows0_2,table55Rows0_3,table55Rows0_4,table55Rows0_5,table55Rows1_0,table55Rows1_1,table55Rows1_2,table55Rows1_3,table55Rows1_4,table55Rows1_5,table55Rows2_0,table55Rows2_1,table55Rows2_2,table55Rows2_3,table55Rows2_4,table55Rows2_5,table55Rows3_0,table55Rows3_1,table55Rows3_2,table55Rows3_3,table55Rows3_4,table55Rows3_5,table55Rows4_0,table55Rows4_1,table55Rows4_2,table55Rows4_3,table55Rows4_4,table55Rows4_5,table55Rows5_0,table55Rows5_1,table55Rows5_2,table55Rows5_3,table55Rows5_4,table55Rows5_5,table55Rows6_0,table55Rows6_1,table55Rows6_2,table55Rows6_3,table55Rows6_4,table55Rows6_5,table55Rows7_0,table55Rows7_1,table55Rows7_2,table55Rows7_3,table55Rows7_4,table55Rows7_5,table55Rows8_0,table55Rows8_1,table55Rows8_2,table55Rows8_3,table55Rows8_4,table55Rows8_5]
    root8Node52Domains0 root8Node52Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node52Step1Chunk0_0_checked, root8Node52Step1Chunk0_1_checked, root8Node52Step1Chunk0_2_checked, root8Node52Step1Chunk0_3_checked, root8Node52Step1Chunk0_4_checked, root8Node52Step1Chunk0_5_checked, root8Node52Step1Chunk1_0_checked, root8Node52Step1Chunk1_1_checked, root8Node52Step1Chunk1_2_checked, root8Node52Step1Chunk1_3_checked, root8Node52Step1Chunk1_4_checked, root8Node52Step1Chunk1_5_checked, root8Node52Step1Chunk2_0_checked, root8Node52Step1Chunk2_1_checked, root8Node52Step1Chunk2_2_checked, root8Node52Step1Chunk2_3_checked, root8Node52Step1Chunk2_4_checked, root8Node52Step1Chunk2_5_checked, root8Node52Step1Chunk3_0_checked, root8Node52Step1Chunk3_1_checked, root8Node52Step1Chunk3_2_checked, root8Node52Step1Chunk3_3_checked, root8Node52Step1Chunk3_4_checked, root8Node52Step1Chunk3_5_checked, root8Node52Step1Chunk4_0_checked, root8Node52Step1Chunk4_1_checked, root8Node52Step1Chunk4_2_checked, root8Node52Step1Chunk4_3_checked, root8Node52Step1Chunk4_4_checked, root8Node52Step1Chunk4_5_checked, root8Node52Step1Chunk5_0_checked, root8Node52Step1Chunk5_1_checked, root8Node52Step1Chunk5_2_checked, root8Node52Step1Chunk5_3_checked, root8Node52Step1Chunk5_4_checked, root8Node52Step1Chunk5_5_checked, root8Node52Step1Chunk6_0_checked, root8Node52Step1Chunk6_1_checked, root8Node52Step1Chunk6_2_checked, root8Node52Step1Chunk6_3_checked, root8Node52Step1Chunk6_4_checked, root8Node52Step1Chunk6_5_checked, root8Node52Step1Chunk7_0_checked, root8Node52Step1Chunk7_1_checked, root8Node52Step1Chunk7_2_checked, root8Node52Step1Chunk7_3_checked, root8Node52Step1Chunk7_4_checked, root8Node52Step1Chunk7_5_checked, root8Node52Step1Chunk8_0_checked, root8Node52Step1Chunk8_1_checked, root8Node52Step1Chunk8_2_checked, root8Node52Step1Chunk8_3_checked, root8Node52Step1Chunk8_4_checked, root8Node52Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node52Step1_checked :
    checkReplacement table55 root8Node52Domains0 root8Node52Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node52Domains0 root8Node52Domains1
    root8Node52Domains0Fast root8Node52Domains1Fast
    root8Node52Domains0_fast_eq root8Node52Domains1_fast_eq
    root8Node52Step1Narrowing_checked (by decide)
def root8Node52Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(2,2)]
  | 30 => [(4,3)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(0,1)]
  | 40 => [(1,4),(7,4)]
  | 41 => [(6,3)]
  | 42 => [(2,2)]
  | 43 => [(3,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(0,2)]
  | 52 => [(1,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(1,0)]
  | 88 => [(2,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node52Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(4,3)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(6,3)]
  | 42 => some [(2,2)]
  | 43 => some [(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,2)]
  | 52 => some [(1,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(1,0)]
  | 88 => some [(2,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node52Domains2_fast_eq : root8Node52Domains2 = expandDomains root8Node52Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node52Domains2 v = expandDomains root8Node52Domains2Fast v from by decide) v
theorem root8Node52Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq (by decide)
theorem root8Node52Step2Narrowing_checked :
    checkNarrowing table56 root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node52Domains1 root8Node52Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node52Step2Chunk0_0_checked, root8Node52Step2Chunk0_1_checked, root8Node52Step2Chunk0_2_checked, root8Node52Step2Chunk0_3_checked, root8Node52Step2Chunk0_4_checked, root8Node52Step2Chunk0_5_checked, root8Node52Step2Chunk1_0_checked, root8Node52Step2Chunk1_1_checked, root8Node52Step2Chunk1_2_checked, root8Node52Step2Chunk1_3_checked, root8Node52Step2Chunk1_4_checked, root8Node52Step2Chunk1_5_checked, root8Node52Step2Chunk2_0_checked, root8Node52Step2Chunk2_1_checked, root8Node52Step2Chunk2_2_checked, root8Node52Step2Chunk2_3_checked, root8Node52Step2Chunk2_4_checked, root8Node52Step2Chunk2_5_checked, root8Node52Step2Chunk3_0_checked, root8Node52Step2Chunk3_1_checked, root8Node52Step2Chunk3_2_checked, root8Node52Step2Chunk3_3_checked, root8Node52Step2Chunk3_4_checked, root8Node52Step2Chunk3_5_checked, root8Node52Step2Chunk4_0_checked, root8Node52Step2Chunk4_1_checked, root8Node52Step2Chunk4_2_checked, root8Node52Step2Chunk4_3_checked, root8Node52Step2Chunk4_4_checked, root8Node52Step2Chunk4_5_checked, root8Node52Step2Chunk5_0_checked, root8Node52Step2Chunk5_1_checked, root8Node52Step2Chunk5_2_checked, root8Node52Step2Chunk5_3_checked, root8Node52Step2Chunk5_4_checked, root8Node52Step2Chunk5_5_checked, root8Node52Step2Chunk6_0_checked, root8Node52Step2Chunk6_1_checked, root8Node52Step2Chunk6_2_checked, root8Node52Step2Chunk6_3_checked, root8Node52Step2Chunk6_4_checked, root8Node52Step2Chunk6_5_checked, root8Node52Step2Chunk7_0_checked, root8Node52Step2Chunk7_1_checked, root8Node52Step2Chunk7_2_checked, root8Node52Step2Chunk7_3_checked, root8Node52Step2Chunk7_4_checked, root8Node52Step2Chunk7_5_checked, root8Node52Step2Chunk8_0_checked, root8Node52Step2Chunk8_1_checked, root8Node52Step2Chunk8_2_checked, root8Node52Step2Chunk8_3_checked, root8Node52Step2Chunk8_4_checked, root8Node52Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node52Step2_checked :
    checkReplacement table56 root8Node52Domains1 root8Node52Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node52Domains1 root8Node52Domains2
    root8Node52Domains1Fast root8Node52Domains2Fast
    root8Node52Domains1_fast_eq root8Node52Domains2_fast_eq
    root8Node52Step2Narrowing_checked (by decide)
def root8Node52Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(8,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(2,2)]
  | 30 => [(4,3)]
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(4,1)]
  | 37 => [(0,2)]
  | 38 => [(1,1)]
  | 39 => [(0,1)]
  | 40 => [(7,4)]
  | 41 => [(6,3)]
  | 42 => [(2,2)]
  | 43 => [(3,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(5,2)]
  | 48 => [(5,0)]
  | 49 => [(4,5)]
  | 50 => [(1,0)]
  | 51 => [(0,2)]
  | 52 => [(1,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(8,4)]
  | 59 => [(0,0)]
  | 60 => [(7,2)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(1,5)]
  | 69 => [(6,1)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(6,1)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5)]
  | 87 => [(1,0)]
  | 88 => [(2,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node52Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(2,2)]
  | 30 => some [(4,3)]
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1)]
  | 37 => some [(0,2)]
  | 38 => some [(1,1)]
  | 39 => some [(0,1)]
  | 40 => some [(7,4)]
  | 41 => some [(6,3)]
  | 42 => some [(2,2)]
  | 43 => some [(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(5,2)]
  | 48 => some [(5,0)]
  | 49 => some [(4,5)]
  | 50 => some [(1,0)]
  | 51 => some [(0,2)]
  | 52 => some [(1,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(8,4)]
  | 59 => some [(0,0)]
  | 60 => some [(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(1,5)]
  | 69 => some [(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5)]
  | 87 => some [(1,0)]
  | 88 => some [(2,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node52Domains3_fast_eq : root8Node52Domains3 = expandDomains root8Node52Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node52Domains3 v = expandDomains root8Node52Domains3Fast v from by decide) v
theorem root8Node52Step3Chunk0_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_0⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk0_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_1⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk0_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_2⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk0_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_3⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk0_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_4⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk0_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows0_5⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk1_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_0⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk1_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_1⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk1_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_2⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk1_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_3⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk1_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_4⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk1_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows1_5⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk2_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_0⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk2_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_1⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk2_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_2⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk2_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_3⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk2_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_4⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk2_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows2_5⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk3_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_0⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk3_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_1⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk3_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_2⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk3_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_3⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk3_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_4⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk3_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows3_5⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk4_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_0⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk4_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_1⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk4_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_2⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk4_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_3⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk4_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_4⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk4_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows4_5⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk5_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_0⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk5_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_1⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk5_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_2⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk5_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_3⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk5_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_4⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk5_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows5_5⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk6_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_0⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk6_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_1⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk6_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_2⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk6_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_3⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk6_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_4⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk6_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows6_5⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk7_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_0⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk7_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_1⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk7_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_2⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk7_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_3⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk7_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_4⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk7_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows7_5⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk8_0_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_0⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk8_1_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_1⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk8_2_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_2⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk8_3_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_3⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk8_4_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_4⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Chunk8_5_checked :
    checkNarrowing ⟨table6Scope, table6Rows8_5⟩
      root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq (by decide)
theorem root8Node52Step3Narrowing_checked :
    checkNarrowing table6 root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkNarrowing_flatten table6Scope [table6Rows0_0,table6Rows0_1,table6Rows0_2,table6Rows0_3,table6Rows0_4,table6Rows0_5,table6Rows1_0,table6Rows1_1,table6Rows1_2,table6Rows1_3,table6Rows1_4,table6Rows1_5,table6Rows2_0,table6Rows2_1,table6Rows2_2,table6Rows2_3,table6Rows2_4,table6Rows2_5,table6Rows3_0,table6Rows3_1,table6Rows3_2,table6Rows3_3,table6Rows3_4,table6Rows3_5,table6Rows4_0,table6Rows4_1,table6Rows4_2,table6Rows4_3,table6Rows4_4,table6Rows4_5,table6Rows5_0,table6Rows5_1,table6Rows5_2,table6Rows5_3,table6Rows5_4,table6Rows5_5,table6Rows6_0,table6Rows6_1,table6Rows6_2,table6Rows6_3,table6Rows6_4,table6Rows6_5,table6Rows7_0,table6Rows7_1,table6Rows7_2,table6Rows7_3,table6Rows7_4,table6Rows7_5,table6Rows8_0,table6Rows8_1,table6Rows8_2,table6Rows8_3,table6Rows8_4,table6Rows8_5]
    root8Node52Domains2 root8Node52Domains3 (by
      simp only [List.all_cons, List.all_nil, root8Node52Step3Chunk0_0_checked, root8Node52Step3Chunk0_1_checked, root8Node52Step3Chunk0_2_checked, root8Node52Step3Chunk0_3_checked, root8Node52Step3Chunk0_4_checked, root8Node52Step3Chunk0_5_checked, root8Node52Step3Chunk1_0_checked, root8Node52Step3Chunk1_1_checked, root8Node52Step3Chunk1_2_checked, root8Node52Step3Chunk1_3_checked, root8Node52Step3Chunk1_4_checked, root8Node52Step3Chunk1_5_checked, root8Node52Step3Chunk2_0_checked, root8Node52Step3Chunk2_1_checked, root8Node52Step3Chunk2_2_checked, root8Node52Step3Chunk2_3_checked, root8Node52Step3Chunk2_4_checked, root8Node52Step3Chunk2_5_checked, root8Node52Step3Chunk3_0_checked, root8Node52Step3Chunk3_1_checked, root8Node52Step3Chunk3_2_checked, root8Node52Step3Chunk3_3_checked, root8Node52Step3Chunk3_4_checked, root8Node52Step3Chunk3_5_checked, root8Node52Step3Chunk4_0_checked, root8Node52Step3Chunk4_1_checked, root8Node52Step3Chunk4_2_checked, root8Node52Step3Chunk4_3_checked, root8Node52Step3Chunk4_4_checked, root8Node52Step3Chunk4_5_checked, root8Node52Step3Chunk5_0_checked, root8Node52Step3Chunk5_1_checked, root8Node52Step3Chunk5_2_checked, root8Node52Step3Chunk5_3_checked, root8Node52Step3Chunk5_4_checked, root8Node52Step3Chunk5_5_checked, root8Node52Step3Chunk6_0_checked, root8Node52Step3Chunk6_1_checked, root8Node52Step3Chunk6_2_checked, root8Node52Step3Chunk6_3_checked, root8Node52Step3Chunk6_4_checked, root8Node52Step3Chunk6_5_checked, root8Node52Step3Chunk7_0_checked, root8Node52Step3Chunk7_1_checked, root8Node52Step3Chunk7_2_checked, root8Node52Step3Chunk7_3_checked, root8Node52Step3Chunk7_4_checked, root8Node52Step3Chunk7_5_checked, root8Node52Step3Chunk8_0_checked, root8Node52Step3Chunk8_1_checked, root8Node52Step3Chunk8_2_checked, root8Node52Step3Chunk8_3_checked, root8Node52Step3Chunk8_4_checked, root8Node52Step3Chunk8_5_checked, Bool.true_and])
theorem root8Node52Step3_checked :
    checkReplacement table6 root8Node52Domains2 root8Node52Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root8Node52Domains2 root8Node52Domains3
    root8Node52Domains2Fast root8Node52Domains3Fast
    root8Node52Domains2_fast_eq root8Node52Domains3_fast_eq
    root8Node52Step3Narrowing_checked (by decide)
theorem root8Node52Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node52Domains3 (.output 25) = true := by decide
def root8Node53Domains0 : Domains 91 State := restrict root8Node37Domains4 3 (8,4)
def root8Node53Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0),(1,3)]
  | 5 => some [(7,2),(8,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5),(6,5)]
  | 11 => some [(0,4),(6,1)]
  | 12 => some [(5,1),(5,4)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3),(8,3)]
  | 20 => some [(7,5),(8,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3),(6,3)]
  | 29 => some [(2,2),(4,2),(8,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5),(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(4,1),(8,1)]
  | 37 => some [(0,2),(6,5)]
  | 38 => some [(0,4),(1,1)]
  | 39 => some [(0,1),(1,4),(3,4),(5,4)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(0,5),(6,3)]
  | 42 => some [(2,2),(2,4)]
  | 43 => some [(1,3),(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3),(8,3)]
  | 47 => some [(5,2),(5,5)]
  | 48 => some [(3,0),(5,0),(7,0)]
  | 49 => some [(2,3),(2,5),(4,3),(4,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0)]
  | 51 => some [(0,2),(6,0)]
  | 52 => some [(1,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4),(6,4)]
  | 57 => some [(0,5),(1,2)]
  | 58 => some [(4,4),(8,4)]
  | 59 => some [(0,0),(1,4),(6,4)]
  | 60 => some [(0,5),(1,2),(7,2)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3),(6,0)]
  | 67 => some [(7,1),(8,1)]
  | 68 => some [(1,5),(7,5)]
  | 69 => some [(0,3),(6,0),(6,1)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0),(7,4)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(4,2),(8,2)]
  | 75 => some [(5,0),(5,3),(8,0)]
  | 76 => some [(4,5),(5,5),(7,3),(8,5)]
  | 77 => some [(4,2),(7,0),(8,2)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1),(8,1)]
  | 80 => some [(0,1),(6,5)]
  | 81 => some [(0,4),(6,2)]
  | 82 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => some [(0,0),(0,5),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => some [(0,3),(1,1),(6,1),(7,1)]
theorem root8Node53Domains0_fast_eq : root8Node53Domains0 = expandDomains root8Node53Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node53Domains0 v = expandDomains root8Node53Domains0Fast v from by decide) v
def root8Node53Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(7,2)]
  | 6 => [(7,1)]
  | 7 => [(7,5)]
  | 8 => [(0,3)]
  | 9 => [(8,1)]
  | 10 => [(1,5)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(8,0)]
  | 14 => [(7,3)]
  | 15 => [(4,2)]
  | 16 => [(5,3)]
  | 17 => [(8,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(5,4)]
  | 22 => [(6,4)]
  | 23 => [(1,2)]
  | 24 => [(7,4)]
  | 25 => [(6,3)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(4,3)]
  | 31 => [(3,5),(7,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(5,4)]
  | 40 => [(1,4),(7,4)]
  | 41 => [(0,5),(6,3)]
  | 42 => [(2,2),(2,4)]
  | 43 => [(1,3),(3,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(7,0)]
  | 49 => [(4,3)]
  | 50 => [(1,5),(3,5)]
  | 51 => [(0,2),(6,0)]
  | 52 => [(1,1),(7,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(1,4)]
  | 60 => [(0,5)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(6,0)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0),(7,4)]
  | 73 => [(1,3),(7,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(8,2)]
  | 78 => [(6,1)]
  | 79 => [(5,1),(8,1)]
  | 80 => [(0,1),(6,5)]
  | 81 => [(0,4),(6,2)]
  | 82 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => [(0,0),(0,5),(6,3),(6,4)]
  | 84 => [(1,2),(4,4),(7,2)]
  | 85 => [(8,3)]
  | 86 => [(5,5),(8,5)]
  | 87 => [(1,0),(3,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => [(0,3),(1,1),(6,1),(7,1)]
def root8Node53Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(7,2)]
  | 6 => some [(7,1)]
  | 7 => some [(7,5)]
  | 8 => some [(0,3)]
  | 9 => some [(8,1)]
  | 10 => some [(1,5)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(8,0)]
  | 14 => some [(7,3)]
  | 15 => some [(4,2)]
  | 16 => some [(5,3)]
  | 17 => some [(8,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(5,4)]
  | 22 => some [(6,4)]
  | 23 => some [(1,2)]
  | 24 => some [(7,4)]
  | 25 => some [(6,3)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(4,3)]
  | 31 => some [(3,5),(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(1,4),(7,4)]
  | 41 => some [(0,5),(6,3)]
  | 42 => some [(2,2),(2,4)]
  | 43 => some [(1,3),(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(1,5),(3,5)]
  | 51 => some [(0,2),(6,0)]
  | 52 => some [(1,1),(7,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0),(7,4)]
  | 73 => some [(1,3),(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1),(8,1)]
  | 80 => some [(0,1),(6,5)]
  | 81 => some [(0,4),(6,2)]
  | 82 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 83 => some [(0,0),(0,5),(6,3),(6,4)]
  | 84 => some [(1,2),(4,4),(7,2)]
  | 85 => some [(8,3)]
  | 86 => some [(5,5),(8,5)]
  | 87 => some [(1,0),(3,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 89 => some [(0,2),(1,5),(3,5),(6,0),(7,5)]
  | _ => some [(0,3),(1,1),(6,1),(7,1)]
theorem root8Node53Domains1_fast_eq : root8Node53Domains1 = expandDomains root8Node53Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node53Domains1 v = expandDomains root8Node53Domains1Fast v from by decide) v
theorem root8Node53Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq (by decide)
theorem root8Node53Step1Narrowing_checked :
    checkNarrowing table36 root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkNarrowing_flatten table36Scope [table36Rows0_0,table36Rows0_1,table36Rows0_2,table36Rows0_3,table36Rows0_4,table36Rows0_5,table36Rows1_0,table36Rows1_1,table36Rows1_2,table36Rows1_3,table36Rows1_4,table36Rows1_5,table36Rows2_0,table36Rows2_1,table36Rows2_2,table36Rows2_3,table36Rows2_4,table36Rows2_5,table36Rows3_0,table36Rows3_1,table36Rows3_2,table36Rows3_3,table36Rows3_4,table36Rows3_5,table36Rows4_0,table36Rows4_1,table36Rows4_2,table36Rows4_3,table36Rows4_4,table36Rows4_5,table36Rows5_0,table36Rows5_1,table36Rows5_2,table36Rows5_3,table36Rows5_4,table36Rows5_5,table36Rows6_0,table36Rows6_1,table36Rows6_2,table36Rows6_3,table36Rows6_4,table36Rows6_5,table36Rows7_0,table36Rows7_1,table36Rows7_2,table36Rows7_3,table36Rows7_4,table36Rows7_5,table36Rows8_0,table36Rows8_1,table36Rows8_2,table36Rows8_3,table36Rows8_4,table36Rows8_5]
    root8Node53Domains0 root8Node53Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node53Step1Chunk0_0_checked, root8Node53Step1Chunk0_1_checked, root8Node53Step1Chunk0_2_checked, root8Node53Step1Chunk0_3_checked, root8Node53Step1Chunk0_4_checked, root8Node53Step1Chunk0_5_checked, root8Node53Step1Chunk1_0_checked, root8Node53Step1Chunk1_1_checked, root8Node53Step1Chunk1_2_checked, root8Node53Step1Chunk1_3_checked, root8Node53Step1Chunk1_4_checked, root8Node53Step1Chunk1_5_checked, root8Node53Step1Chunk2_0_checked, root8Node53Step1Chunk2_1_checked, root8Node53Step1Chunk2_2_checked, root8Node53Step1Chunk2_3_checked, root8Node53Step1Chunk2_4_checked, root8Node53Step1Chunk2_5_checked, root8Node53Step1Chunk3_0_checked, root8Node53Step1Chunk3_1_checked, root8Node53Step1Chunk3_2_checked, root8Node53Step1Chunk3_3_checked, root8Node53Step1Chunk3_4_checked, root8Node53Step1Chunk3_5_checked, root8Node53Step1Chunk4_0_checked, root8Node53Step1Chunk4_1_checked, root8Node53Step1Chunk4_2_checked, root8Node53Step1Chunk4_3_checked, root8Node53Step1Chunk4_4_checked, root8Node53Step1Chunk4_5_checked, root8Node53Step1Chunk5_0_checked, root8Node53Step1Chunk5_1_checked, root8Node53Step1Chunk5_2_checked, root8Node53Step1Chunk5_3_checked, root8Node53Step1Chunk5_4_checked, root8Node53Step1Chunk5_5_checked, root8Node53Step1Chunk6_0_checked, root8Node53Step1Chunk6_1_checked, root8Node53Step1Chunk6_2_checked, root8Node53Step1Chunk6_3_checked, root8Node53Step1Chunk6_4_checked, root8Node53Step1Chunk6_5_checked, root8Node53Step1Chunk7_0_checked, root8Node53Step1Chunk7_1_checked, root8Node53Step1Chunk7_2_checked, root8Node53Step1Chunk7_3_checked, root8Node53Step1Chunk7_4_checked, root8Node53Step1Chunk7_5_checked, root8Node53Step1Chunk8_0_checked, root8Node53Step1Chunk8_1_checked, root8Node53Step1Chunk8_2_checked, root8Node53Step1Chunk8_3_checked, root8Node53Step1Chunk8_4_checked, root8Node53Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node53Step1_checked :
    checkReplacement table36 root8Node53Domains0 root8Node53Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node53Domains0 root8Node53Domains1
    root8Node53Domains0Fast root8Node53Domains1Fast
    root8Node53Domains0_fast_eq root8Node53Domains1_fast_eq
    root8Node53Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
