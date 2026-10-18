module

public import SpectreFinite.RadiusFiveRoot8Part38
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable54
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node101Domains0 : Domains 91 State := restrict root8Node100Domains1 21 (0,1)
def root8Node101Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(1,3),(3,3),(7,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(0,1)]
  | 22 => some [(0,4),(6,2)]
  | 23 => some [(5,4),(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0),(7,0)]
  | 32 => some [(4,3),(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(6,5)]
  | 69 => some [(0,4),(1,1)]
  | 70 => some [(0,5),(1,3),(6,3)]
  | 71 => some [(4,4),(7,2),(8,2)]
  | 72 => some [(1,4),(4,0),(7,4),(8,0)]
  | 73 => some [(0,5),(1,3),(6,3),(7,3)]
  | 74 => some [(2,2),(2,4),(4,2)]
  | 75 => some [(1,3),(3,3),(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(0,4),(1,1),(7,1)]
  | 79 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => some [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(4,3),(7,3),(8,3)]
  | 86 => some [(3,5),(5,2),(5,5),(8,2)]
  | 87 => some [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => some [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node101Domains0_fast_eq : root8Node101Domains0 = expandDomains root8Node101Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node101Domains0 v = expandDomains root8Node101Domains0Fast v from by decide) v
def root8Node101Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(3,4)]
  | 13 => [(3,3),(7,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3)]
  | 20 => [(0,2)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3),(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(0,2),(6,5)]
  | 69 => [(0,4),(1,1)]
  | 70 => [(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(0,4),(1,1)]
  | 79 => [(5,1),(5,4)]
  | 80 => [(0,1),(6,4)]
  | 81 => [(1,2),(6,2)]
  | 82 => [(7,4)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(2,1),(4,1)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node101Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(3,3),(7,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(0,2),(6,5)]
  | 69 => some [(0,4),(1,1)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(5,2),(5,5),(8,5)]
  | 77 => some [(7,0),(8,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(0,4),(0,5),(6,2),(6,3)]
  | 84 => some [(4,4),(5,4),(7,2),(8,4)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1)]
  | 89 => some [(0,2),(1,0),(6,0),(7,0)]
  | _ => some [(1,1),(4,3),(7,1)]
theorem root8Node101Domains1_fast_eq : root8Node101Domains1 = expandDomains root8Node101Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node101Domains1 v = expandDomains root8Node101Domains1Fast v from by decide) v
theorem root8Node101Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq (by decide)
theorem root8Node101Step1Narrowing_checked :
    checkNarrowing table54 root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node101Domains0 root8Node101Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node101Step1Chunk0_0_checked, root8Node101Step1Chunk0_1_checked, root8Node101Step1Chunk0_2_checked, root8Node101Step1Chunk0_3_checked, root8Node101Step1Chunk0_4_checked, root8Node101Step1Chunk0_5_checked, root8Node101Step1Chunk1_0_checked, root8Node101Step1Chunk1_1_checked, root8Node101Step1Chunk1_2_checked, root8Node101Step1Chunk1_3_checked, root8Node101Step1Chunk1_4_checked, root8Node101Step1Chunk1_5_checked, root8Node101Step1Chunk2_0_checked, root8Node101Step1Chunk2_1_checked, root8Node101Step1Chunk2_2_checked, root8Node101Step1Chunk2_3_checked, root8Node101Step1Chunk2_4_checked, root8Node101Step1Chunk2_5_checked, root8Node101Step1Chunk3_0_checked, root8Node101Step1Chunk3_1_checked, root8Node101Step1Chunk3_2_checked, root8Node101Step1Chunk3_3_checked, root8Node101Step1Chunk3_4_checked, root8Node101Step1Chunk3_5_checked, root8Node101Step1Chunk4_0_checked, root8Node101Step1Chunk4_1_checked, root8Node101Step1Chunk4_2_checked, root8Node101Step1Chunk4_3_checked, root8Node101Step1Chunk4_4_checked, root8Node101Step1Chunk4_5_checked, root8Node101Step1Chunk5_0_checked, root8Node101Step1Chunk5_1_checked, root8Node101Step1Chunk5_2_checked, root8Node101Step1Chunk5_3_checked, root8Node101Step1Chunk5_4_checked, root8Node101Step1Chunk5_5_checked, root8Node101Step1Chunk6_0_checked, root8Node101Step1Chunk6_1_checked, root8Node101Step1Chunk6_2_checked, root8Node101Step1Chunk6_3_checked, root8Node101Step1Chunk6_4_checked, root8Node101Step1Chunk6_5_checked, root8Node101Step1Chunk7_0_checked, root8Node101Step1Chunk7_1_checked, root8Node101Step1Chunk7_2_checked, root8Node101Step1Chunk7_3_checked, root8Node101Step1Chunk7_4_checked, root8Node101Step1Chunk7_5_checked, root8Node101Step1Chunk8_0_checked, root8Node101Step1Chunk8_1_checked, root8Node101Step1Chunk8_2_checked, root8Node101Step1Chunk8_3_checked, root8Node101Step1Chunk8_4_checked, root8Node101Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node101Step1_checked :
    checkReplacement table54 root8Node101Domains0 root8Node101Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node101Domains0 root8Node101Domains1
    root8Node101Domains0Fast root8Node101Domains1Fast
    root8Node101Domains0_fast_eq root8Node101Domains1_fast_eq
    root8Node101Step1Narrowing_checked (by decide)
def root8Node101Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(3,4)]
  | 13 => [(3,3),(7,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3)]
  | 20 => [(0,2)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(1,3),(6,3)]
  | 71 => [(7,2),(8,2)]
  | 72 => [(4,0),(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4),(1,1)]
  | 79 => [(5,1),(5,4)]
  | 80 => [(0,1),(6,4)]
  | 81 => [(1,2),(6,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3),(8,3)]
  | 86 => [(3,5),(5,5)]
  | 87 => [(0,3),(1,0)]
  | 88 => [(2,1),(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node101Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(3,3),(7,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node101Domains2_fast_eq : root8Node101Domains2 = expandDomains root8Node101Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node101Domains2 v = expandDomains root8Node101Domains2Fast v from by decide) v
theorem root8Node101Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq (by decide)
theorem root8Node101Step2Narrowing_checked :
    checkNarrowing table56 root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root8Node101Domains1 root8Node101Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node101Step2Chunk0_0_checked, root8Node101Step2Chunk0_1_checked, root8Node101Step2Chunk0_2_checked, root8Node101Step2Chunk0_3_checked, root8Node101Step2Chunk0_4_checked, root8Node101Step2Chunk0_5_checked, root8Node101Step2Chunk1_0_checked, root8Node101Step2Chunk1_1_checked, root8Node101Step2Chunk1_2_checked, root8Node101Step2Chunk1_3_checked, root8Node101Step2Chunk1_4_checked, root8Node101Step2Chunk1_5_checked, root8Node101Step2Chunk2_0_checked, root8Node101Step2Chunk2_1_checked, root8Node101Step2Chunk2_2_checked, root8Node101Step2Chunk2_3_checked, root8Node101Step2Chunk2_4_checked, root8Node101Step2Chunk2_5_checked, root8Node101Step2Chunk3_0_checked, root8Node101Step2Chunk3_1_checked, root8Node101Step2Chunk3_2_checked, root8Node101Step2Chunk3_3_checked, root8Node101Step2Chunk3_4_checked, root8Node101Step2Chunk3_5_checked, root8Node101Step2Chunk4_0_checked, root8Node101Step2Chunk4_1_checked, root8Node101Step2Chunk4_2_checked, root8Node101Step2Chunk4_3_checked, root8Node101Step2Chunk4_4_checked, root8Node101Step2Chunk4_5_checked, root8Node101Step2Chunk5_0_checked, root8Node101Step2Chunk5_1_checked, root8Node101Step2Chunk5_2_checked, root8Node101Step2Chunk5_3_checked, root8Node101Step2Chunk5_4_checked, root8Node101Step2Chunk5_5_checked, root8Node101Step2Chunk6_0_checked, root8Node101Step2Chunk6_1_checked, root8Node101Step2Chunk6_2_checked, root8Node101Step2Chunk6_3_checked, root8Node101Step2Chunk6_4_checked, root8Node101Step2Chunk6_5_checked, root8Node101Step2Chunk7_0_checked, root8Node101Step2Chunk7_1_checked, root8Node101Step2Chunk7_2_checked, root8Node101Step2Chunk7_3_checked, root8Node101Step2Chunk7_4_checked, root8Node101Step2Chunk7_5_checked, root8Node101Step2Chunk8_0_checked, root8Node101Step2Chunk8_1_checked, root8Node101Step2Chunk8_2_checked, root8Node101Step2Chunk8_3_checked, root8Node101Step2Chunk8_4_checked, root8Node101Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node101Step2_checked :
    checkReplacement table56 root8Node101Domains1 root8Node101Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node101Domains1 root8Node101Domains2
    root8Node101Domains1Fast root8Node101Domains2Fast
    root8Node101Domains1_fast_eq root8Node101Domains2_fast_eq
    root8Node101Step2Narrowing_checked (by decide)
def root8Node102Domains0 : Domains 91 State := restrict root8Node101Domains2 13 (3,3)
def root8Node102Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(3,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3),(6,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node102Domains0_fast_eq : root8Node102Domains0 = expandDomains root8Node102Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node102Domains0 v = expandDomains root8Node102Domains0Fast v from by decide) v
def root8Node103Domains0 : Domains 91 State := restrict root8Node102Domains0 70 (1,3)
def root8Node103Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(3,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(7,2),(8,2)]
  | 72 => some [(4,0),(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4),(1,1)]
  | 79 => some [(5,1),(5,4)]
  | 80 => some [(0,1),(6,4)]
  | 81 => some [(1,2),(6,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3),(8,3)]
  | 86 => some [(3,5),(5,5)]
  | 87 => some [(0,3),(1,0)]
  | 88 => some [(2,1),(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node103Domains0_fast_eq : root8Node103Domains0 = expandDomains root8Node103Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node103Domains0 v = expandDomains root8Node103Domains0Fast v from by decide) v
def root8Node103Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(3,4)]
  | 13 => [(3,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3)]
  | 20 => [(0,2)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0)]
  | 32 => [(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3)]
  | 60 => [(8,2)]
  | 61 => [(8,3)]
  | 62 => [(8,5)]
  | 63 => [(1,0)]
  | 64 => [(7,1)]
  | 65 => [(7,5)]
  | 66 => [(0,3)]
  | 67 => [(8,1)]
  | 68 => [(6,5)]
  | 69 => [(0,4)]
  | 70 => [(1,3)]
  | 71 => [(8,2)]
  | 72 => [(8,0)]
  | 73 => [(7,3)]
  | 74 => [(4,2)]
  | 75 => [(5,3)]
  | 76 => [(8,5)]
  | 77 => [(7,0)]
  | 78 => [(0,4)]
  | 79 => [(5,4)]
  | 80 => [(6,4)]
  | 81 => [(1,2)]
  | 82 => [(7,4)]
  | 83 => [(6,3)]
  | 84 => [(7,2)]
  | 85 => [(4,3)]
  | 86 => [(3,5)]
  | 87 => [(0,3)]
  | 88 => [(4,1)]
  | 89 => [(0,2)]
  | _ => [(1,1)]
def root8Node103Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4)]
  | 13 => some [(3,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3)]
  | 20 => some [(0,2)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0)]
  | 32 => some [(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2)]
  | 48 => some [(5,3)]
  | 49 => some [(8,5)]
  | 50 => some [(1,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4)]
  | 59 => some [(1,3)]
  | 60 => some [(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(8,5)]
  | 63 => some [(1,0)]
  | 64 => some [(7,1)]
  | 65 => some [(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(8,1)]
  | 68 => some [(6,5)]
  | 69 => some [(0,4)]
  | 70 => some [(1,3)]
  | 71 => some [(8,2)]
  | 72 => some [(8,0)]
  | 73 => some [(7,3)]
  | 74 => some [(4,2)]
  | 75 => some [(5,3)]
  | 76 => some [(8,5)]
  | 77 => some [(7,0)]
  | 78 => some [(0,4)]
  | 79 => some [(5,4)]
  | 80 => some [(6,4)]
  | 81 => some [(1,2)]
  | 82 => some [(7,4)]
  | 83 => some [(6,3)]
  | 84 => some [(7,2)]
  | 85 => some [(4,3)]
  | 86 => some [(3,5)]
  | 87 => some [(0,3)]
  | 88 => some [(4,1)]
  | 89 => some [(0,2)]
  | _ => some [(1,1)]
theorem root8Node103Domains1_fast_eq : root8Node103Domains1 = expandDomains root8Node103Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node103Domains1 v = expandDomains root8Node103Domains1Fast v from by decide) v
theorem root8Node103Step1Chunk0_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_0⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk0_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_1⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk0_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_2⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk0_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_3⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk0_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_4⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk0_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows0_5⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk1_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_0⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk1_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_1⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk1_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_2⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk1_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_3⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk1_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_4⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk1_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows1_5⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk2_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_0⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk2_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_1⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk2_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_2⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk2_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_3⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk2_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_4⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk2_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows2_5⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk3_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_0⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk3_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_1⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk3_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_2⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk3_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_3⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk3_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_4⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk3_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows3_5⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk4_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_0⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk4_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_1⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk4_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_2⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk4_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_3⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk4_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_4⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk4_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows4_5⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk5_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_0⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk5_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_1⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk5_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_2⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk5_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_3⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk5_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_4⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk5_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows5_5⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk6_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_0⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk6_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_1⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk6_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_2⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk6_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_3⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk6_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_4⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk6_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows6_5⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk7_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_0⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk7_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_1⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk7_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_2⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk7_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_3⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk7_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_4⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk7_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows7_5⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk8_0_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_0⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk8_1_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_1⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk8_2_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_2⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk8_3_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_3⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk8_4_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_4⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Chunk8_5_checked :
    checkNarrowing ⟨table54Scope, table54Rows8_5⟩
      root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq (by decide)
theorem root8Node103Step1Narrowing_checked :
    checkNarrowing table54 root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkNarrowing_flatten table54Scope [table54Rows0_0,table54Rows0_1,table54Rows0_2,table54Rows0_3,table54Rows0_4,table54Rows0_5,table54Rows1_0,table54Rows1_1,table54Rows1_2,table54Rows1_3,table54Rows1_4,table54Rows1_5,table54Rows2_0,table54Rows2_1,table54Rows2_2,table54Rows2_3,table54Rows2_4,table54Rows2_5,table54Rows3_0,table54Rows3_1,table54Rows3_2,table54Rows3_3,table54Rows3_4,table54Rows3_5,table54Rows4_0,table54Rows4_1,table54Rows4_2,table54Rows4_3,table54Rows4_4,table54Rows4_5,table54Rows5_0,table54Rows5_1,table54Rows5_2,table54Rows5_3,table54Rows5_4,table54Rows5_5,table54Rows6_0,table54Rows6_1,table54Rows6_2,table54Rows6_3,table54Rows6_4,table54Rows6_5,table54Rows7_0,table54Rows7_1,table54Rows7_2,table54Rows7_3,table54Rows7_4,table54Rows7_5,table54Rows8_0,table54Rows8_1,table54Rows8_2,table54Rows8_3,table54Rows8_4,table54Rows8_5]
    root8Node103Domains0 root8Node103Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node103Step1Chunk0_0_checked, root8Node103Step1Chunk0_1_checked, root8Node103Step1Chunk0_2_checked, root8Node103Step1Chunk0_3_checked, root8Node103Step1Chunk0_4_checked, root8Node103Step1Chunk0_5_checked, root8Node103Step1Chunk1_0_checked, root8Node103Step1Chunk1_1_checked, root8Node103Step1Chunk1_2_checked, root8Node103Step1Chunk1_3_checked, root8Node103Step1Chunk1_4_checked, root8Node103Step1Chunk1_5_checked, root8Node103Step1Chunk2_0_checked, root8Node103Step1Chunk2_1_checked, root8Node103Step1Chunk2_2_checked, root8Node103Step1Chunk2_3_checked, root8Node103Step1Chunk2_4_checked, root8Node103Step1Chunk2_5_checked, root8Node103Step1Chunk3_0_checked, root8Node103Step1Chunk3_1_checked, root8Node103Step1Chunk3_2_checked, root8Node103Step1Chunk3_3_checked, root8Node103Step1Chunk3_4_checked, root8Node103Step1Chunk3_5_checked, root8Node103Step1Chunk4_0_checked, root8Node103Step1Chunk4_1_checked, root8Node103Step1Chunk4_2_checked, root8Node103Step1Chunk4_3_checked, root8Node103Step1Chunk4_4_checked, root8Node103Step1Chunk4_5_checked, root8Node103Step1Chunk5_0_checked, root8Node103Step1Chunk5_1_checked, root8Node103Step1Chunk5_2_checked, root8Node103Step1Chunk5_3_checked, root8Node103Step1Chunk5_4_checked, root8Node103Step1Chunk5_5_checked, root8Node103Step1Chunk6_0_checked, root8Node103Step1Chunk6_1_checked, root8Node103Step1Chunk6_2_checked, root8Node103Step1Chunk6_3_checked, root8Node103Step1Chunk6_4_checked, root8Node103Step1Chunk6_5_checked, root8Node103Step1Chunk7_0_checked, root8Node103Step1Chunk7_1_checked, root8Node103Step1Chunk7_2_checked, root8Node103Step1Chunk7_3_checked, root8Node103Step1Chunk7_4_checked, root8Node103Step1Chunk7_5_checked, root8Node103Step1Chunk8_0_checked, root8Node103Step1Chunk8_1_checked, root8Node103Step1Chunk8_2_checked, root8Node103Step1Chunk8_3_checked, root8Node103Step1Chunk8_4_checked, root8Node103Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node103Step1_checked :
    checkReplacement table54 root8Node103Domains0 root8Node103Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node103Domains0 root8Node103Domains1
    root8Node103Domains0Fast root8Node103Domains1Fast
    root8Node103Domains0_fast_eq root8Node103Domains1_fast_eq
    root8Node103Step1Narrowing_checked (by decide)
theorem root8Node103Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node103Domains1 (.output 49) = true := by decide
end SpectreFinite.HexSearch.RadiusFive
