module

public import SpectreFinite.RadiusFiveRoot8Part22
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable35
public import SpectreFinite.RadiusFiveTable54

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node57Domains0 : Domains 91 State := restrict root8Node53Domains2 31 (7,5)
def root8Node57Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 31 => some [(7,5)]
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
  | 82 => some [(5,4),(8,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0),(7,0)]
  | 88 => some [(4,3),(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root8Node57Domains0_fast_eq : root8Node57Domains0 = expandDomains root8Node57Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node57Domains0 v = expandDomains root8Node57Domains0Fast v from by decide) v
def root8Node57Domains1 (v : Fin 91) : List State :=
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
  | 31 => [(7,5)]
  | 32 => [(0,3)]
  | 33 => [(4,1)]
  | 34 => [(0,2)]
  | 35 => [(1,1)]
  | 36 => [(8,1)]
  | 37 => [(6,5)]
  | 38 => [(0,4)]
  | 39 => [(5,4)]
  | 40 => [(7,4)]
  | 41 => [(6,3)]
  | 42 => [(2,2)]
  | 43 => [(3,3)]
  | 44 => [(5,2)]
  | 45 => [(8,0)]
  | 46 => [(8,3)]
  | 47 => [(5,5)]
  | 48 => [(7,0)]
  | 49 => [(4,3)]
  | 50 => [(1,5),(3,5)]
  | 51 => [(0,2)]
  | 52 => [(1,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(1,4)]
  | 60 => [(0,5)]
  | 61 => [(5,0)]
  | 62 => [(4,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(6,0)]
  | 67 => [(7,1)]
  | 68 => [(7,5)]
  | 69 => [(6,0)]
  | 70 => [(0,0)]
  | 71 => [(7,2)]
  | 72 => [(4,0)]
  | 73 => [(7,3)]
  | 74 => [(8,2)]
  | 75 => [(8,0)]
  | 76 => [(7,3)]
  | 77 => [(8,2)]
  | 78 => [(6,1)]
  | 79 => [(5,1)]
  | 80 => [(0,1)]
  | 81 => [(6,2)]
  | 82 => [(8,4)]
  | 83 => [(6,4)]
  | 84 => [(1,2)]
  | 85 => [(8,3)]
  | 86 => [(8,5)]
  | 87 => [(1,0)]
  | 88 => [(7,1)]
  | 89 => [(7,5)]
  | _ => [(0,3)]
def root8Node57Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(6,3)]
  | 42 => some [(2,2)]
  | 43 => some [(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(1,5),(3,5)]
  | 51 => some [(0,2)]
  | 52 => some [(1,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root8Node57Domains1_fast_eq : root8Node57Domains1 = expandDomains root8Node57Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node57Domains1 v = expandDomains root8Node57Domains1Fast v from by decide) v
theorem root8Node57Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq (by decide)
theorem root8Node57Step1Narrowing_checked :
    checkNarrowing table54 root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node57Domains0 root8Node57Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node57Step1Chunk0_0_checked, root8Node57Step1Chunk0_1_checked, root8Node57Step1Chunk0_2_checked, root8Node57Step1Chunk0_3_checked, root8Node57Step1Chunk0_4_checked, root8Node57Step1Chunk0_5_checked, root8Node57Step1Chunk1_0_checked, root8Node57Step1Chunk1_1_checked, root8Node57Step1Chunk1_2_checked, root8Node57Step1Chunk1_3_checked, root8Node57Step1Chunk1_4_checked, root8Node57Step1Chunk1_5_checked, root8Node57Step1Chunk2_0_checked, root8Node57Step1Chunk2_1_checked, root8Node57Step1Chunk2_2_checked, root8Node57Step1Chunk2_3_checked, root8Node57Step1Chunk2_4_checked, root8Node57Step1Chunk2_5_checked, root8Node57Step1Chunk3_0_checked, root8Node57Step1Chunk3_1_checked, root8Node57Step1Chunk3_2_checked, root8Node57Step1Chunk3_3_checked, root8Node57Step1Chunk3_4_checked, root8Node57Step1Chunk3_5_checked, root8Node57Step1Chunk4_0_checked, root8Node57Step1Chunk4_1_checked, root8Node57Step1Chunk4_2_checked, root8Node57Step1Chunk4_3_checked, root8Node57Step1Chunk4_4_checked, root8Node57Step1Chunk4_5_checked, root8Node57Step1Chunk5_0_checked, root8Node57Step1Chunk5_1_checked, root8Node57Step1Chunk5_2_checked, root8Node57Step1Chunk5_3_checked, root8Node57Step1Chunk5_4_checked, root8Node57Step1Chunk5_5_checked, root8Node57Step1Chunk6_0_checked, root8Node57Step1Chunk6_1_checked, root8Node57Step1Chunk6_2_checked, root8Node57Step1Chunk6_3_checked, root8Node57Step1Chunk6_4_checked, root8Node57Step1Chunk6_5_checked, root8Node57Step1Chunk7_0_checked, root8Node57Step1Chunk7_1_checked, root8Node57Step1Chunk7_2_checked, root8Node57Step1Chunk7_3_checked, root8Node57Step1Chunk7_4_checked, root8Node57Step1Chunk7_5_checked, root8Node57Step1Chunk8_0_checked, root8Node57Step1Chunk8_1_checked, root8Node57Step1Chunk8_2_checked, root8Node57Step1Chunk8_3_checked, root8Node57Step1Chunk8_4_checked, root8Node57Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node57Step1_checked :
    checkReplacement table54 root8Node57Domains0 root8Node57Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node57Domains0 root8Node57Domains1
    root8Node57Domains0Fast root8Node57Domains1Fast
    root8Node57Domains0_fast_eq root8Node57Domains1_fast_eq
    root8Node57Step1Narrowing_checked (by decide)
def root8Node58Domains0 : Domains 91 State := restrict root8Node57Domains1 50 (1,5)
def root8Node58Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(6,3)]
  | 42 => some [(2,2)]
  | 43 => some [(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(1,5)]
  | 51 => some [(0,2)]
  | 52 => some [(1,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root8Node58Domains0_fast_eq : root8Node58Domains0 = expandDomains root8Node58Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node58Domains0 v = expandDomains root8Node58Domains0Fast v from by decide) v
theorem root8Node58Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node58Domains0 (.output 28) = true := by decide
def root8Node59Domains0 : Domains 91 State := restrict root8Node57Domains1 50 (3,5)
def root8Node59Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 31 => some [(7,5)]
  | 32 => some [(0,3)]
  | 33 => some [(4,1)]
  | 34 => some [(0,2)]
  | 35 => some [(1,1)]
  | 36 => some [(8,1)]
  | 37 => some [(6,5)]
  | 38 => some [(0,4)]
  | 39 => some [(5,4)]
  | 40 => some [(7,4)]
  | 41 => some [(6,3)]
  | 42 => some [(2,2)]
  | 43 => some [(3,3)]
  | 44 => some [(5,2)]
  | 45 => some [(8,0)]
  | 46 => some [(8,3)]
  | 47 => some [(5,5)]
  | 48 => some [(7,0)]
  | 49 => some [(4,3)]
  | 50 => some [(3,5)]
  | 51 => some [(0,2)]
  | 52 => some [(1,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(1,4)]
  | 60 => some [(0,5)]
  | 61 => some [(5,0)]
  | 62 => some [(4,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(6,0)]
  | 67 => some [(7,1)]
  | 68 => some [(7,5)]
  | 69 => some [(6,0)]
  | 70 => some [(0,0)]
  | 71 => some [(7,2)]
  | 72 => some [(4,0)]
  | 73 => some [(7,3)]
  | 74 => some [(8,2)]
  | 75 => some [(8,0)]
  | 76 => some [(7,3)]
  | 77 => some [(8,2)]
  | 78 => some [(6,1)]
  | 79 => some [(5,1)]
  | 80 => some [(0,1)]
  | 81 => some [(6,2)]
  | 82 => some [(8,4)]
  | 83 => some [(6,4)]
  | 84 => some [(1,2)]
  | 85 => some [(8,3)]
  | 86 => some [(8,5)]
  | 87 => some [(1,0)]
  | 88 => some [(7,1)]
  | 89 => some [(7,5)]
  | _ => some [(0,3)]
theorem root8Node59Domains0_fast_eq : root8Node59Domains0 = expandDomains root8Node59Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node59Domains0 v = expandDomains root8Node59Domains0Fast v from by decide) v
theorem root8Node59Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node59Domains0 (.output 29) = true := by decide
def root8Node60Domains0 : Domains 91 State := restrict root8Node0Domains4 35 (7,1)
def root8Node60Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 35 => some [(7,1)]
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
theorem root8Node60Domains0_fast_eq : root8Node60Domains0 = expandDomains root8Node60Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node60Domains0 v = expandDomains root8Node60Domains0Fast v from by decide) v
def root8Node60Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(0,1),(1,4),(3,4),(4,4),(7,4),(8,4)]
  | 1 => [(0,0),(0,5),(6,2),(6,3)]
  | 2 => [(4,4),(7,2),(8,4)]
  | 3 => [(1,4),(7,4)]
  | 4 => [(0,5),(1,3),(6,3)]
  | 5 => [(4,2),(4,4),(7,2),(8,2)]
  | 6 => [(2,1),(2,3),(2,5),(4,1),(4,5),(7,1),(8,1)]
  | 7 => [(0,2),(1,0),(1,5),(6,0)]
  | 8 => [(1,1),(6,1),(7,1)]
  | 9 => [(4,1),(7,5),(8,1)]
  | 10 => [(0,2),(6,0),(6,5)]
  | 11 => [(0,4),(1,1),(7,1)]
  | 12 => [(3,4),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => [(0,0),(1,3),(3,3),(5,0),(5,3),(6,4),(7,3),(8,0)]
  | 14 => [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 15 => [(4,0),(7,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5),(8,2)]
  | 18 => [(7,0),(8,0)]
  | 19 => [(2,3),(4,3),(7,3),(8,3)]
  | 20 => [(0,2),(1,5),(3,5),(4,2),(5,2),(5,5),(8,2)]
  | 21 => [(0,1),(1,4),(1,5),(3,4),(5,4),(6,5),(7,4),(7,5)]
  | 22 => [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 23 => [(4,4),(5,1),(5,4),(8,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(2,0),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 30 => [(2,1),(2,3),(2,5),(4,3),(4,5),(7,3),(8,5)]
  | 31 => [(1,0),(4,2),(6,0),(7,0)]
  | 32 => [(4,3),(5,3),(7,1),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(3,1),(5,1),(7,1),(8,1)]
  | 39 => [(0,1),(1,5),(6,5)]
  | 40 => [(0,0),(1,4),(6,3),(6,4),(7,4)]
  | 41 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 42 => [(4,0),(7,4)]
  | 43 => [(1,3),(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0)]
  | 51 => [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 52 => [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(1,3),(6,3)]
  | 60 => [(0,5),(1,2),(3,2),(7,2),(8,2)]
  | 61 => [(5,0),(5,3),(8,3)]
  | 62 => [(4,5),(5,5),(8,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(1,5),(6,5)]
  | 69 => [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 70 => [(0,0),(0,5),(1,3),(6,3)]
  | 71 => [(4,4),(7,2),(8,2)]
  | 72 => [(1,4),(4,0),(7,4),(8,0)]
  | 73 => [(0,5),(1,3),(6,3),(7,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
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
def root8Node60Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(0,1),(1,4),(3,4),(4,4),(7,4),(8,4)]
  | 1 => some [(0,0),(0,5),(6,2),(6,3)]
  | 2 => some [(4,4),(7,2),(8,4)]
  | 3 => some [(1,4),(7,4)]
  | 4 => some [(0,5),(1,3),(6,3)]
  | 5 => some [(4,2),(4,4),(7,2),(8,2)]
  | 6 => some [(2,1),(2,3),(2,5),(4,1),(4,5),(7,1),(8,1)]
  | 7 => some [(0,2),(1,0),(1,5),(6,0)]
  | 8 => some [(1,1),(6,1),(7,1)]
  | 9 => some [(4,1),(7,5),(8,1)]
  | 10 => some [(0,2),(6,0),(6,5)]
  | 11 => some [(0,4),(1,1),(7,1)]
  | 12 => some [(3,4),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 13 => some [(0,0),(1,3),(3,3),(5,0),(5,3),(6,4),(7,3),(8,0)]
  | 14 => some [(1,2),(3,2),(5,2),(5,5),(7,2)]
  | 15 => some [(4,0),(7,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5),(8,2)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(2,3),(4,3),(7,3),(8,3)]
  | 20 => some [(0,2),(1,5),(3,5),(4,2),(5,2),(5,5),(8,2)]
  | 21 => some [(0,1),(1,4),(1,5),(3,4),(5,4),(6,5),(7,4),(7,5)]
  | 22 => some [(0,3),(0,4),(0,5),(6,1),(6,2)]
  | 23 => some [(4,4),(5,1),(5,4),(8,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0),(4,4),(7,4),(8,4)]
  | 30 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(7,3),(8,5)]
  | 31 => some [(1,0),(4,2),(6,0),(7,0)]
  | 32 => some [(4,3),(5,3),(7,1),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0),(1,4),(6,3),(6,4),(7,4)]
  | 41 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(0,2),(1,0),(1,5),(3,5),(6,0),(7,0)]
  | 51 => some [(0,2),(0,3),(1,1),(6,0),(6,1)]
  | 52 => some [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(0,5),(1,2),(3,2),(7,2),(8,2)]
  | 61 => some [(5,0),(5,3),(8,3)]
  | 62 => some [(4,5),(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,3),(0,4),(1,1),(6,0),(6,1)]
  | 70 => some [(0,0),(0,5),(1,3),(6,3)]
  | 71 => some [(4,4),(7,2),(8,2)]
  | 72 => some [(1,4),(4,0),(7,4),(8,0)]
  | 73 => some [(0,5),(1,3),(6,3),(7,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
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
theorem root8Node60Domains1_fast_eq : root8Node60Domains1 = expandDomains root8Node60Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node60Domains1 v = expandDomains root8Node60Domains1Fast v from by decide) v
theorem root8Node60Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Narrowing_checked :
    checkNarrowing table35 root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_flatten table35Scope [table35Rows0_0,table35Rows0_1,table35Rows0_2,table35Rows0_3,table35Rows0_4,table35Rows0_5,table35Rows1_0,table35Rows1_1,table35Rows1_2,table35Rows1_3,table35Rows1_4,table35Rows1_5,table35Rows2_0,table35Rows2_1,table35Rows2_2,table35Rows2_3,table35Rows2_4,table35Rows2_5,table35Rows3_0,table35Rows3_1,table35Rows3_2,table35Rows3_3,table35Rows3_4,table35Rows3_5,table35Rows4_0,table35Rows4_1,table35Rows4_2,table35Rows4_3,table35Rows4_4,table35Rows4_5,table35Rows5_0,table35Rows5_1,table35Rows5_2,table35Rows5_3,table35Rows5_4,table35Rows5_5,table35Rows6_0,table35Rows6_1,table35Rows6_2,table35Rows6_3,table35Rows6_4,table35Rows6_5,table35Rows7_0,table35Rows7_1,table35Rows7_2,table35Rows7_3,table35Rows7_4,table35Rows7_5,table35Rows8_0,table35Rows8_1,table35Rows8_2,table35Rows8_3,table35Rows8_4,table35Rows8_5]
    root8Node60Domains0 root8Node60Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node60Step1Chunk0_0_checked, root8Node60Step1Chunk0_1_checked, root8Node60Step1Chunk0_2_checked, root8Node60Step1Chunk0_3_checked, root8Node60Step1Chunk0_4_checked, root8Node60Step1Chunk0_5_checked, root8Node60Step1Chunk1_0_checked, root8Node60Step1Chunk1_1_checked, root8Node60Step1Chunk1_2_checked, root8Node60Step1Chunk1_3_checked, root8Node60Step1Chunk1_4_checked, root8Node60Step1Chunk1_5_checked, root8Node60Step1Chunk2_0_checked, root8Node60Step1Chunk2_1_checked, root8Node60Step1Chunk2_2_checked, root8Node60Step1Chunk2_3_checked, root8Node60Step1Chunk2_4_checked, root8Node60Step1Chunk2_5_checked, root8Node60Step1Chunk3_0_checked, root8Node60Step1Chunk3_1_checked, root8Node60Step1Chunk3_2_checked, root8Node60Step1Chunk3_3_checked, root8Node60Step1Chunk3_4_checked, root8Node60Step1Chunk3_5_checked, root8Node60Step1Chunk4_0_checked, root8Node60Step1Chunk4_1_checked, root8Node60Step1Chunk4_2_checked, root8Node60Step1Chunk4_3_checked, root8Node60Step1Chunk4_4_checked, root8Node60Step1Chunk4_5_checked, root8Node60Step1Chunk5_0_checked, root8Node60Step1Chunk5_1_checked, root8Node60Step1Chunk5_2_checked, root8Node60Step1Chunk5_3_checked, root8Node60Step1Chunk5_4_checked, root8Node60Step1Chunk5_5_checked, root8Node60Step1Chunk6_0_checked, root8Node60Step1Chunk6_1_checked, root8Node60Step1Chunk6_2_checked, root8Node60Step1Chunk6_3_checked, root8Node60Step1Chunk6_4_checked, root8Node60Step1Chunk6_5_checked, root8Node60Step1Chunk7_0_checked, root8Node60Step1Chunk7_1_checked, root8Node60Step1Chunk7_2_checked, root8Node60Step1Chunk7_3_checked, root8Node60Step1Chunk7_4_checked, root8Node60Step1Chunk7_5_checked, root8Node60Step1Chunk8_0_checked, root8Node60Step1Chunk8_1_checked, root8Node60Step1Chunk8_2_checked, root8Node60Step1Chunk8_3_checked, root8Node60Step1Chunk8_4_checked, root8Node60Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node60Step1_checked :
    checkReplacement table35 root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq
    root8Node60Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
