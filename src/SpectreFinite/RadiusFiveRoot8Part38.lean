module

public import SpectreFinite.RadiusFiveRoot8Part37
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable21
public import SpectreFinite.RadiusFiveTable25
public import SpectreFinite.RadiusFiveTable27
public import SpectreFinite.RadiusFiveTable5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node98Domains0 : Domains 91 State := restrict root8Node86Domains2 0 (7,4)
def root8Node98Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3),(6,3)]
  | 5 => some [(4,2),(7,2),(8,2)]
  | 6 => some [(2,1),(2,3),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(8,1)]
  | 10 => some [(0,2),(6,5)]
  | 11 => some [(0,4),(1,1)]
  | 12 => some [(3,4),(4,1),(5,1),(5,4),(8,1)]
  | 13 => some [(0,0),(1,3),(3,3),(6,4),(7,3)]
  | 14 => some [(1,2),(3,2),(5,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(2,3),(4,3),(7,3),(8,3)]
  | 20 => some [(0,2),(1,5),(3,5),(5,2),(5,5)]
  | 21 => some [(0,1),(1,5),(6,5),(7,5)]
  | 22 => some [(0,3),(0,4),(6,1),(6,2)]
  | 23 => some [(5,1),(5,4),(8,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0),(4,4),(8,4)]
  | 30 => some [(4,5),(7,3)]
  | 31 => some [(1,0),(4,2),(7,0)]
  | 32 => some [(4,3),(5,3),(7,1),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0),(6,4)]
  | 41 => some [(1,2),(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(0,3),(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(5,3),(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
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
theorem root8Node98Domains0_fast_eq : root8Node98Domains0 = expandDomains root8Node98Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node98Domains0 v = expandDomains root8Node98Domains0Fast v from by decide) v
def root8Node98Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3),(6,3)]
  | 5 => [(4,2),(7,2),(8,2)]
  | 6 => [(2,1),(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(4,1),(8,1)]
  | 10 => [(0,2),(6,5)]
  | 11 => [(0,4),(1,1)]
  | 12 => [(3,4),(4,1),(5,1),(5,4),(8,1)]
  | 13 => [(0,0),(1,3),(3,3),(7,3)]
  | 14 => [(3,2),(5,2)]
  | 15 => [(4,0),(8,0)]
  | 16 => [(7,3),(8,3)]
  | 17 => [(5,2),(5,5)]
  | 18 => [(7,0),(8,0)]
  | 19 => [(2,3),(4,3),(7,3),(8,3)]
  | 20 => [(0,2),(1,5),(3,5),(5,2),(5,5)]
  | 21 => [(0,1),(1,5),(6,5)]
  | 22 => [(0,4),(6,1),(6,2)]
  | 23 => [(5,1),(5,4),(8,4)]
  | 24 => [(0,1),(1,4)]
  | 25 => [(0,5),(6,2)]
  | 26 => [(4,4),(8,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(2,0),(2,4),(4,0),(4,4),(8,4)]
  | 30 => [(4,5)]
  | 31 => [(1,0),(7,0)]
  | 32 => [(4,3),(7,1),(8,3)]
  | 33 => [(7,5),(8,5)]
  | 34 => [(1,0),(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(3,1),(5,1),(7,1),(8,1)]
  | 39 => [(0,1),(1,5),(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0),(7,4)]
  | 43 => [(1,3),(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1),(8,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(1,3),(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(1,5),(6,5)]
  | 69 => [(0,4),(1,1),(6,1)]
  | 70 => [(0,5),(1,3),(6,3)]
  | 71 => [(4,4),(7,2),(8,2)]
  | 72 => [(1,4),(4,0),(7,4),(8,0)]
  | 73 => [(0,5),(1,3),(6,3),(7,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(0,4),(1,1),(7,1)]
  | 79 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(4,3),(7,3),(8,3)]
  | 86 => [(3,5),(5,2),(5,5),(8,2)]
  | 87 => [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node98Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3),(6,3)]
  | 5 => some [(4,2),(7,2),(8,2)]
  | 6 => some [(2,1),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(8,1)]
  | 10 => some [(0,2),(6,5)]
  | 11 => some [(0,4),(1,1)]
  | 12 => some [(3,4),(4,1),(5,1),(5,4),(8,1)]
  | 13 => some [(0,0),(1,3),(3,3),(7,3)]
  | 14 => some [(3,2),(5,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(2,3),(4,3),(7,3),(8,3)]
  | 20 => some [(0,2),(1,5),(3,5),(5,2),(5,5)]
  | 21 => some [(0,1),(1,5),(6,5)]
  | 22 => some [(0,4),(6,1),(6,2)]
  | 23 => some [(5,1),(5,4),(8,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0),(4,4),(8,4)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0),(7,0)]
  | 32 => some [(4,3),(7,1),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
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
theorem root8Node98Domains1_fast_eq : root8Node98Domains1 = expandDomains root8Node98Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node98Domains1 v = expandDomains root8Node98Domains1Fast v from by decide) v
theorem root8Node98Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq (by decide)
theorem root8Node98Step1Narrowing_checked :
    checkNarrowing table21 root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkNarrowing_flatten table21Scope [table21Rows0_0,table21Rows0_1,table21Rows0_2,table21Rows0_3,table21Rows0_4,table21Rows0_5,table21Rows1_0,table21Rows1_1,table21Rows1_2,table21Rows1_3,table21Rows1_4,table21Rows1_5,table21Rows2_0,table21Rows2_1,table21Rows2_2,table21Rows2_3,table21Rows2_4,table21Rows2_5,table21Rows3_0,table21Rows3_1,table21Rows3_2,table21Rows3_3,table21Rows3_4,table21Rows3_5,table21Rows4_0,table21Rows4_1,table21Rows4_2,table21Rows4_3,table21Rows4_4,table21Rows4_5,table21Rows5_0,table21Rows5_1,table21Rows5_2,table21Rows5_3,table21Rows5_4,table21Rows5_5,table21Rows6_0,table21Rows6_1,table21Rows6_2,table21Rows6_3,table21Rows6_4,table21Rows6_5,table21Rows7_0,table21Rows7_1,table21Rows7_2,table21Rows7_3,table21Rows7_4,table21Rows7_5,table21Rows8_0,table21Rows8_1,table21Rows8_2,table21Rows8_3,table21Rows8_4,table21Rows8_5]
    root8Node98Domains0 root8Node98Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node98Step1Chunk0_0_checked, root8Node98Step1Chunk0_1_checked, root8Node98Step1Chunk0_2_checked, root8Node98Step1Chunk0_3_checked, root8Node98Step1Chunk0_4_checked, root8Node98Step1Chunk0_5_checked, root8Node98Step1Chunk1_0_checked, root8Node98Step1Chunk1_1_checked, root8Node98Step1Chunk1_2_checked, root8Node98Step1Chunk1_3_checked, root8Node98Step1Chunk1_4_checked, root8Node98Step1Chunk1_5_checked, root8Node98Step1Chunk2_0_checked, root8Node98Step1Chunk2_1_checked, root8Node98Step1Chunk2_2_checked, root8Node98Step1Chunk2_3_checked, root8Node98Step1Chunk2_4_checked, root8Node98Step1Chunk2_5_checked, root8Node98Step1Chunk3_0_checked, root8Node98Step1Chunk3_1_checked, root8Node98Step1Chunk3_2_checked, root8Node98Step1Chunk3_3_checked, root8Node98Step1Chunk3_4_checked, root8Node98Step1Chunk3_5_checked, root8Node98Step1Chunk4_0_checked, root8Node98Step1Chunk4_1_checked, root8Node98Step1Chunk4_2_checked, root8Node98Step1Chunk4_3_checked, root8Node98Step1Chunk4_4_checked, root8Node98Step1Chunk4_5_checked, root8Node98Step1Chunk5_0_checked, root8Node98Step1Chunk5_1_checked, root8Node98Step1Chunk5_2_checked, root8Node98Step1Chunk5_3_checked, root8Node98Step1Chunk5_4_checked, root8Node98Step1Chunk5_5_checked, root8Node98Step1Chunk6_0_checked, root8Node98Step1Chunk6_1_checked, root8Node98Step1Chunk6_2_checked, root8Node98Step1Chunk6_3_checked, root8Node98Step1Chunk6_4_checked, root8Node98Step1Chunk6_5_checked, root8Node98Step1Chunk7_0_checked, root8Node98Step1Chunk7_1_checked, root8Node98Step1Chunk7_2_checked, root8Node98Step1Chunk7_3_checked, root8Node98Step1Chunk7_4_checked, root8Node98Step1Chunk7_5_checked, root8Node98Step1Chunk8_0_checked, root8Node98Step1Chunk8_1_checked, root8Node98Step1Chunk8_2_checked, root8Node98Step1Chunk8_3_checked, root8Node98Step1Chunk8_4_checked, root8Node98Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node98Step1_checked :
    checkReplacement table21 root8Node98Domains0 root8Node98Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node98Domains0 root8Node98Domains1
    root8Node98Domains0Fast root8Node98Domains1Fast
    root8Node98Domains0_fast_eq root8Node98Domains1_fast_eq
    root8Node98Step1Narrowing_checked (by decide)
def root8Node99Domains0 : Domains 91 State := restrict root8Node98Domains1 4 (1,3)
def root8Node99Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2),(7,2),(8,2)]
  | 6 => some [(2,1),(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(4,1),(8,1)]
  | 10 => some [(0,2),(6,5)]
  | 11 => some [(0,4),(1,1)]
  | 12 => some [(3,4),(4,1),(5,1),(5,4),(8,1)]
  | 13 => some [(0,0),(1,3),(3,3),(7,3)]
  | 14 => some [(3,2),(5,2)]
  | 15 => some [(4,0),(8,0)]
  | 16 => some [(7,3),(8,3)]
  | 17 => some [(5,2),(5,5)]
  | 18 => some [(7,0),(8,0)]
  | 19 => some [(2,3),(4,3),(7,3),(8,3)]
  | 20 => some [(0,2),(1,5),(3,5),(5,2),(5,5)]
  | 21 => some [(0,1),(1,5),(6,5)]
  | 22 => some [(0,4),(6,1),(6,2)]
  | 23 => some [(5,1),(5,4),(8,4)]
  | 24 => some [(0,1),(1,4)]
  | 25 => some [(0,5),(6,2)]
  | 26 => some [(4,4),(8,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0),(4,4),(8,4)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0),(7,0)]
  | 32 => some [(4,3),(7,1),(8,3)]
  | 33 => some [(7,5),(8,5)]
  | 34 => some [(1,0),(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1),(8,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
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
theorem root8Node99Domains0_fast_eq : root8Node99Domains0 = expandDomains root8Node99Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node99Domains0 v = expandDomains root8Node99Domains0Fast v from by decide) v
def root8Node99Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2),(8,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(3,4),(5,4)]
  | 13 => [(1,3),(3,3),(7,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3),(4,3)]
  | 20 => [(0,2),(1,5),(3,5)]
  | 21 => [(0,1),(6,5)]
  | 22 => [(0,4),(6,2)]
  | 23 => [(5,4),(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(2,0),(2,4),(4,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0),(7,0)]
  | 32 => [(4,3),(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(3,1),(5,1),(7,1)]
  | 39 => [(0,1),(1,5),(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0),(7,4)]
  | 43 => [(1,3),(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1),(8,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(1,3),(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(1,5),(6,5)]
  | 69 => [(0,4),(1,1),(6,1)]
  | 70 => [(0,5),(1,3),(6,3)]
  | 71 => [(4,4),(7,2),(8,2)]
  | 72 => [(1,4),(4,0),(7,4),(8,0)]
  | 73 => [(0,5),(1,3),(6,3),(7,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(0,4),(1,1),(7,1)]
  | 79 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(4,3),(7,3),(8,3)]
  | 86 => [(3,5),(5,2),(5,5),(8,2)]
  | 87 => [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node99Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2),(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4),(5,4)]
  | 13 => some [(1,3),(3,3),(7,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5)]
  | 21 => some [(0,1),(6,5)]
  | 22 => some [(0,4),(6,2)]
  | 23 => some [(5,4),(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0),(7,0)]
  | 32 => some [(4,3),(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1)]
  | 39 => some [(0,1),(1,5),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
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
theorem root8Node99Domains1_fast_eq : root8Node99Domains1 = expandDomains root8Node99Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node99Domains1 v = expandDomains root8Node99Domains1Fast v from by decide) v
theorem root8Node99Step1Chunk0_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_0⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk0_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_1⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk0_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_2⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk0_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_3⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk0_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_4⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk0_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows0_5⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk1_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_0⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk1_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_1⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk1_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_2⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk1_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_3⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk1_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_4⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk1_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows1_5⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk2_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_0⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk2_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_1⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk2_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_2⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk2_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_3⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk2_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_4⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk2_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows2_5⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk3_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_0⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk3_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_1⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk3_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_2⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk3_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_3⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk3_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_4⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk3_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows3_5⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk4_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_0⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk4_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_1⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk4_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_2⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk4_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_3⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk4_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_4⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk4_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows4_5⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk5_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_0⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk5_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_1⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk5_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_2⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk5_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_3⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk5_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_4⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk5_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows5_5⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk6_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_0⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk6_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_1⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk6_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_2⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk6_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_3⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk6_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_4⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk6_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows6_5⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk7_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_0⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk7_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_1⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk7_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_2⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk7_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_3⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk7_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_4⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk7_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows7_5⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk8_0_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_0⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk8_1_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_1⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk8_2_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_2⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk8_3_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_3⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk8_4_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_4⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Chunk8_5_checked :
    checkNarrowing ⟨table25Scope, table25Rows8_5⟩
      root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq (by decide)
theorem root8Node99Step1Narrowing_checked :
    checkNarrowing table25 root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkNarrowing_flatten table25Scope [table25Rows0_0,table25Rows0_1,table25Rows0_2,table25Rows0_3,table25Rows0_4,table25Rows0_5,table25Rows1_0,table25Rows1_1,table25Rows1_2,table25Rows1_3,table25Rows1_4,table25Rows1_5,table25Rows2_0,table25Rows2_1,table25Rows2_2,table25Rows2_3,table25Rows2_4,table25Rows2_5,table25Rows3_0,table25Rows3_1,table25Rows3_2,table25Rows3_3,table25Rows3_4,table25Rows3_5,table25Rows4_0,table25Rows4_1,table25Rows4_2,table25Rows4_3,table25Rows4_4,table25Rows4_5,table25Rows5_0,table25Rows5_1,table25Rows5_2,table25Rows5_3,table25Rows5_4,table25Rows5_5,table25Rows6_0,table25Rows6_1,table25Rows6_2,table25Rows6_3,table25Rows6_4,table25Rows6_5,table25Rows7_0,table25Rows7_1,table25Rows7_2,table25Rows7_3,table25Rows7_4,table25Rows7_5,table25Rows8_0,table25Rows8_1,table25Rows8_2,table25Rows8_3,table25Rows8_4,table25Rows8_5]
    root8Node99Domains0 root8Node99Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node99Step1Chunk0_0_checked, root8Node99Step1Chunk0_1_checked, root8Node99Step1Chunk0_2_checked, root8Node99Step1Chunk0_3_checked, root8Node99Step1Chunk0_4_checked, root8Node99Step1Chunk0_5_checked, root8Node99Step1Chunk1_0_checked, root8Node99Step1Chunk1_1_checked, root8Node99Step1Chunk1_2_checked, root8Node99Step1Chunk1_3_checked, root8Node99Step1Chunk1_4_checked, root8Node99Step1Chunk1_5_checked, root8Node99Step1Chunk2_0_checked, root8Node99Step1Chunk2_1_checked, root8Node99Step1Chunk2_2_checked, root8Node99Step1Chunk2_3_checked, root8Node99Step1Chunk2_4_checked, root8Node99Step1Chunk2_5_checked, root8Node99Step1Chunk3_0_checked, root8Node99Step1Chunk3_1_checked, root8Node99Step1Chunk3_2_checked, root8Node99Step1Chunk3_3_checked, root8Node99Step1Chunk3_4_checked, root8Node99Step1Chunk3_5_checked, root8Node99Step1Chunk4_0_checked, root8Node99Step1Chunk4_1_checked, root8Node99Step1Chunk4_2_checked, root8Node99Step1Chunk4_3_checked, root8Node99Step1Chunk4_4_checked, root8Node99Step1Chunk4_5_checked, root8Node99Step1Chunk5_0_checked, root8Node99Step1Chunk5_1_checked, root8Node99Step1Chunk5_2_checked, root8Node99Step1Chunk5_3_checked, root8Node99Step1Chunk5_4_checked, root8Node99Step1Chunk5_5_checked, root8Node99Step1Chunk6_0_checked, root8Node99Step1Chunk6_1_checked, root8Node99Step1Chunk6_2_checked, root8Node99Step1Chunk6_3_checked, root8Node99Step1Chunk6_4_checked, root8Node99Step1Chunk6_5_checked, root8Node99Step1Chunk7_0_checked, root8Node99Step1Chunk7_1_checked, root8Node99Step1Chunk7_2_checked, root8Node99Step1Chunk7_3_checked, root8Node99Step1Chunk7_4_checked, root8Node99Step1Chunk7_5_checked, root8Node99Step1Chunk8_0_checked, root8Node99Step1Chunk8_1_checked, root8Node99Step1Chunk8_2_checked, root8Node99Step1Chunk8_3_checked, root8Node99Step1Chunk8_4_checked, root8Node99Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node99Step1_checked :
    checkReplacement table25 root8Node99Domains0 root8Node99Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node99Domains0 root8Node99Domains1
    root8Node99Domains0Fast root8Node99Domains1Fast
    root8Node99Domains0_fast_eq root8Node99Domains1_fast_eq
    root8Node99Step1Narrowing_checked (by decide)
def root8Node99Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,2),(8,2)]
  | 6 => [(4,1)]
  | 7 => [(0,2)]
  | 8 => [(1,1)]
  | 9 => [(8,1)]
  | 10 => [(6,5)]
  | 11 => [(0,4)]
  | 12 => [(3,4),(5,4)]
  | 13 => [(1,3),(3,3),(7,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3),(4,3)]
  | 20 => [(0,2),(1,5),(3,5)]
  | 21 => [(0,1),(6,5)]
  | 22 => [(0,4),(6,2)]
  | 23 => [(5,4),(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(1,4),(6,4)]
  | 28 => [(0,5),(1,2)]
  | 29 => [(2,0),(2,4),(4,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0),(7,0)]
  | 32 => [(4,3),(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3),(6,0)]
  | 38 => [(3,1),(5,1),(7,1)]
  | 39 => [(0,1),(6,5)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0),(7,4)]
  | 43 => [(1,3),(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2),(8,2)]
  | 48 => [(5,0),(5,3)]
  | 49 => [(4,5),(8,5)]
  | 50 => [(1,0),(7,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1),(8,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4),(8,4)]
  | 59 => [(0,0),(1,3),(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(1,5),(6,5)]
  | 69 => [(0,4),(1,1),(6,1)]
  | 70 => [(0,5),(1,3),(6,3)]
  | 71 => [(4,4),(7,2),(8,2)]
  | 72 => [(1,4),(4,0),(7,4),(8,0)]
  | 73 => [(0,5),(1,3),(6,3),(7,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(0,4),(1,1),(7,1)]
  | 79 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(4,3),(7,3),(8,3)]
  | 86 => [(3,5),(5,2),(5,5),(8,2)]
  | 87 => [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node99Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,2),(8,2)]
  | 6 => some [(4,1)]
  | 7 => some [(0,2)]
  | 8 => some [(1,1)]
  | 9 => some [(8,1)]
  | 10 => some [(6,5)]
  | 11 => some [(0,4)]
  | 12 => some [(3,4),(5,4)]
  | 13 => some [(1,3),(3,3),(7,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5)]
  | 21 => some [(0,1),(6,5)]
  | 22 => some [(0,4),(6,2)]
  | 23 => some [(5,4),(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0),(7,0)]
  | 32 => some [(4,3),(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
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
theorem root8Node99Domains2_fast_eq : root8Node99Domains2 = expandDomains root8Node99Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node99Domains2 v = expandDomains root8Node99Domains2Fast v from by decide) v
theorem root8Node99Step2Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq (by decide)
theorem root8Node99Step2Narrowing_checked :
    checkNarrowing table5 root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkNarrowing_flatten table5Scope [table5Rows0_0,table5Rows0_1,table5Rows0_2,table5Rows0_3,table5Rows0_4,table5Rows0_5,table5Rows1_0,table5Rows1_1,table5Rows1_2,table5Rows1_3,table5Rows1_4,table5Rows1_5,table5Rows2_0,table5Rows2_1,table5Rows2_2,table5Rows2_3,table5Rows2_4,table5Rows2_5,table5Rows3_0,table5Rows3_1,table5Rows3_2,table5Rows3_3,table5Rows3_4,table5Rows3_5,table5Rows4_0,table5Rows4_1,table5Rows4_2,table5Rows4_3,table5Rows4_4,table5Rows4_5,table5Rows5_0,table5Rows5_1,table5Rows5_2,table5Rows5_3,table5Rows5_4,table5Rows5_5,table5Rows6_0,table5Rows6_1,table5Rows6_2,table5Rows6_3,table5Rows6_4,table5Rows6_5,table5Rows7_0,table5Rows7_1,table5Rows7_2,table5Rows7_3,table5Rows7_4,table5Rows7_5,table5Rows8_0,table5Rows8_1,table5Rows8_2,table5Rows8_3,table5Rows8_4,table5Rows8_5]
    root8Node99Domains1 root8Node99Domains2 (by
      simp only [List.all_cons, List.all_nil, root8Node99Step2Chunk0_0_checked, root8Node99Step2Chunk0_1_checked, root8Node99Step2Chunk0_2_checked, root8Node99Step2Chunk0_3_checked, root8Node99Step2Chunk0_4_checked, root8Node99Step2Chunk0_5_checked, root8Node99Step2Chunk1_0_checked, root8Node99Step2Chunk1_1_checked, root8Node99Step2Chunk1_2_checked, root8Node99Step2Chunk1_3_checked, root8Node99Step2Chunk1_4_checked, root8Node99Step2Chunk1_5_checked, root8Node99Step2Chunk2_0_checked, root8Node99Step2Chunk2_1_checked, root8Node99Step2Chunk2_2_checked, root8Node99Step2Chunk2_3_checked, root8Node99Step2Chunk2_4_checked, root8Node99Step2Chunk2_5_checked, root8Node99Step2Chunk3_0_checked, root8Node99Step2Chunk3_1_checked, root8Node99Step2Chunk3_2_checked, root8Node99Step2Chunk3_3_checked, root8Node99Step2Chunk3_4_checked, root8Node99Step2Chunk3_5_checked, root8Node99Step2Chunk4_0_checked, root8Node99Step2Chunk4_1_checked, root8Node99Step2Chunk4_2_checked, root8Node99Step2Chunk4_3_checked, root8Node99Step2Chunk4_4_checked, root8Node99Step2Chunk4_5_checked, root8Node99Step2Chunk5_0_checked, root8Node99Step2Chunk5_1_checked, root8Node99Step2Chunk5_2_checked, root8Node99Step2Chunk5_3_checked, root8Node99Step2Chunk5_4_checked, root8Node99Step2Chunk5_5_checked, root8Node99Step2Chunk6_0_checked, root8Node99Step2Chunk6_1_checked, root8Node99Step2Chunk6_2_checked, root8Node99Step2Chunk6_3_checked, root8Node99Step2Chunk6_4_checked, root8Node99Step2Chunk6_5_checked, root8Node99Step2Chunk7_0_checked, root8Node99Step2Chunk7_1_checked, root8Node99Step2Chunk7_2_checked, root8Node99Step2Chunk7_3_checked, root8Node99Step2Chunk7_4_checked, root8Node99Step2Chunk7_5_checked, root8Node99Step2Chunk8_0_checked, root8Node99Step2Chunk8_1_checked, root8Node99Step2Chunk8_2_checked, root8Node99Step2Chunk8_3_checked, root8Node99Step2Chunk8_4_checked, root8Node99Step2Chunk8_5_checked, Bool.true_and])
theorem root8Node99Step2_checked :
    checkReplacement table5 root8Node99Domains1 root8Node99Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root8Node99Domains1 root8Node99Domains2
    root8Node99Domains1Fast root8Node99Domains2Fast
    root8Node99Domains1_fast_eq root8Node99Domains2_fast_eq
    root8Node99Step2Narrowing_checked (by decide)
def root8Node100Domains0 : Domains 91 State := restrict root8Node99Domains2 5 (4,2)
def root8Node100Domains0Fast (v : Fin 91) : Option (List State) :=
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
  | 12 => some [(3,4),(5,4)]
  | 13 => some [(1,3),(3,3),(7,3)]
  | 14 => some [(5,2)]
  | 15 => some [(8,0)]
  | 16 => some [(8,3)]
  | 17 => some [(5,5)]
  | 18 => some [(7,0)]
  | 19 => some [(2,3),(4,3)]
  | 20 => some [(0,2),(1,5),(3,5)]
  | 21 => some [(0,1),(6,5)]
  | 22 => some [(0,4),(6,2)]
  | 23 => some [(5,4),(8,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(4,4)]
  | 27 => some [(1,4),(6,4)]
  | 28 => some [(0,5),(1,2)]
  | 29 => some [(2,0),(2,4),(4,0)]
  | 30 => some [(4,5)]
  | 31 => some [(1,0),(7,0)]
  | 32 => some [(4,3),(7,1)]
  | 33 => some [(7,5)]
  | 34 => some [(6,0)]
  | 35 => some [(7,1)]
  | 36 => some [(7,5)]
  | 37 => some [(0,3),(6,0)]
  | 38 => some [(3,1),(5,1),(7,1)]
  | 39 => some [(0,1),(6,5)]
  | 40 => some [(0,0)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0),(7,4)]
  | 43 => some [(1,3),(7,3)]
  | 44 => some [(8,2)]
  | 45 => some [(8,0)]
  | 46 => some [(7,3)]
  | 47 => some [(4,2),(8,2)]
  | 48 => some [(5,0),(5,3)]
  | 49 => some [(4,5),(8,5)]
  | 50 => some [(1,0),(7,0)]
  | 51 => some [(6,1)]
  | 52 => some [(5,1),(8,1)]
  | 53 => some [(0,1),(6,5)]
  | 54 => some [(0,4),(6,2)]
  | 55 => some [(5,4),(8,4)]
  | 56 => some [(6,4)]
  | 57 => some [(1,2)]
  | 58 => some [(7,4),(8,4)]
  | 59 => some [(0,0),(1,3),(6,3)]
  | 60 => some [(7,2),(8,2)]
  | 61 => some [(8,3)]
  | 62 => some [(5,5),(8,5)]
  | 63 => some [(1,0),(7,0)]
  | 64 => some [(4,3),(7,1)]
  | 65 => some [(3,5),(7,5)]
  | 66 => some [(0,3)]
  | 67 => some [(4,1),(8,1)]
  | 68 => some [(0,2),(1,5),(6,5)]
  | 69 => some [(0,4),(1,1),(6,1)]
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
theorem root8Node100Domains0_fast_eq : root8Node100Domains0 = expandDomains root8Node100Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node100Domains0 v = expandDomains root8Node100Domains0Fast v from by decide) v
def root8Node100Domains1 (v : Fin 91) : List State :=
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
  | 13 => [(1,3),(3,3),(7,3)]
  | 14 => [(5,2)]
  | 15 => [(8,0)]
  | 16 => [(8,3)]
  | 17 => [(5,5)]
  | 18 => [(7,0)]
  | 19 => [(2,3)]
  | 20 => [(0,2)]
  | 21 => [(0,1),(6,5)]
  | 22 => [(0,4),(6,2)]
  | 23 => [(5,4),(8,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(4,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(4,0)]
  | 30 => [(4,5)]
  | 31 => [(1,0),(7,0)]
  | 32 => [(4,3),(7,1)]
  | 33 => [(7,5)]
  | 34 => [(6,0)]
  | 35 => [(7,1)]
  | 36 => [(7,5)]
  | 37 => [(0,3)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(0,0)]
  | 41 => [(7,2)]
  | 42 => [(4,0),(7,4)]
  | 43 => [(1,3),(7,3)]
  | 44 => [(8,2)]
  | 45 => [(8,0)]
  | 46 => [(7,3)]
  | 47 => [(4,2)]
  | 48 => [(5,3)]
  | 49 => [(8,5)]
  | 50 => [(1,0)]
  | 51 => [(6,1)]
  | 52 => [(5,1),(8,1)]
  | 53 => [(0,1),(6,5)]
  | 54 => [(0,4),(6,2)]
  | 55 => [(5,4),(8,4)]
  | 56 => [(6,4)]
  | 57 => [(1,2)]
  | 58 => [(7,4)]
  | 59 => [(1,3),(6,3)]
  | 60 => [(7,2),(8,2)]
  | 61 => [(8,3)]
  | 62 => [(5,5),(8,5)]
  | 63 => [(1,0),(7,0)]
  | 64 => [(4,3),(7,1)]
  | 65 => [(3,5),(7,5)]
  | 66 => [(0,3)]
  | 67 => [(4,1),(8,1)]
  | 68 => [(0,2),(6,5)]
  | 69 => [(0,4),(1,1)]
  | 70 => [(0,5),(1,3),(6,3)]
  | 71 => [(4,4),(7,2),(8,2)]
  | 72 => [(1,4),(4,0),(7,4),(8,0)]
  | 73 => [(0,5),(1,3),(6,3),(7,3)]
  | 74 => [(2,2),(2,4),(4,2)]
  | 75 => [(1,3),(3,3),(5,3)]
  | 76 => [(5,2),(5,5),(8,5)]
  | 77 => [(7,0),(8,0)]
  | 78 => [(0,4),(1,1),(7,1)]
  | 79 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 80 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 81 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 82 => [(0,1),(1,4),(3,4),(6,5),(7,4)]
  | 83 => [(0,4),(0,5),(6,2),(6,3)]
  | 84 => [(4,4),(5,4),(7,2),(8,4)]
  | 85 => [(4,3),(7,3),(8,3)]
  | 86 => [(3,5),(5,2),(5,5),(8,2)]
  | 87 => [(0,3),(1,0),(3,0),(5,0),(7,0)]
  | 88 => [(2,1),(2,3),(2,5),(4,1),(4,5)]
  | 89 => [(0,2),(1,0),(6,0),(7,0)]
  | _ => [(1,1),(4,3),(7,1)]
def root8Node100Domains1Fast (v : Fin 91) : Option (List State) :=
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
  | 21 => some [(0,1),(6,5)]
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
theorem root8Node100Domains1_fast_eq : root8Node100Domains1 = expandDomains root8Node100Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root8Node100Domains1 v = expandDomains root8Node100Domains1Fast v from by decide) v
theorem root8Node100Step1Chunk0_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk0_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk0_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk0_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk0_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk0_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows0_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk1_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows1_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk2_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows2_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk3_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows3_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk4_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows4_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk5_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows5_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk6_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows6_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk7_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows7_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_0_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_0⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_1_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_1⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_2_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_2⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_3_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_3⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_4_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_4⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Chunk8_5_checked :
    checkNarrowing ⟨table27Scope, table27Rows8_5⟩
      root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq (by decide)
theorem root8Node100Step1Narrowing_checked :
    checkNarrowing table27 root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkNarrowing_flatten table27Scope [table27Rows0_0,table27Rows0_1,table27Rows0_2,table27Rows0_3,table27Rows0_4,table27Rows0_5,table27Rows1_0,table27Rows1_1,table27Rows1_2,table27Rows1_3,table27Rows1_4,table27Rows1_5,table27Rows2_0,table27Rows2_1,table27Rows2_2,table27Rows2_3,table27Rows2_4,table27Rows2_5,table27Rows3_0,table27Rows3_1,table27Rows3_2,table27Rows3_3,table27Rows3_4,table27Rows3_5,table27Rows4_0,table27Rows4_1,table27Rows4_2,table27Rows4_3,table27Rows4_4,table27Rows4_5,table27Rows5_0,table27Rows5_1,table27Rows5_2,table27Rows5_3,table27Rows5_4,table27Rows5_5,table27Rows6_0,table27Rows6_1,table27Rows6_2,table27Rows6_3,table27Rows6_4,table27Rows6_5,table27Rows7_0,table27Rows7_1,table27Rows7_2,table27Rows7_3,table27Rows7_4,table27Rows7_5,table27Rows8_0,table27Rows8_1,table27Rows8_2,table27Rows8_3,table27Rows8_4,table27Rows8_5]
    root8Node100Domains0 root8Node100Domains1 (by
      simp only [List.all_cons, List.all_nil, root8Node100Step1Chunk0_0_checked, root8Node100Step1Chunk0_1_checked, root8Node100Step1Chunk0_2_checked, root8Node100Step1Chunk0_3_checked, root8Node100Step1Chunk0_4_checked, root8Node100Step1Chunk0_5_checked, root8Node100Step1Chunk1_0_checked, root8Node100Step1Chunk1_1_checked, root8Node100Step1Chunk1_2_checked, root8Node100Step1Chunk1_3_checked, root8Node100Step1Chunk1_4_checked, root8Node100Step1Chunk1_5_checked, root8Node100Step1Chunk2_0_checked, root8Node100Step1Chunk2_1_checked, root8Node100Step1Chunk2_2_checked, root8Node100Step1Chunk2_3_checked, root8Node100Step1Chunk2_4_checked, root8Node100Step1Chunk2_5_checked, root8Node100Step1Chunk3_0_checked, root8Node100Step1Chunk3_1_checked, root8Node100Step1Chunk3_2_checked, root8Node100Step1Chunk3_3_checked, root8Node100Step1Chunk3_4_checked, root8Node100Step1Chunk3_5_checked, root8Node100Step1Chunk4_0_checked, root8Node100Step1Chunk4_1_checked, root8Node100Step1Chunk4_2_checked, root8Node100Step1Chunk4_3_checked, root8Node100Step1Chunk4_4_checked, root8Node100Step1Chunk4_5_checked, root8Node100Step1Chunk5_0_checked, root8Node100Step1Chunk5_1_checked, root8Node100Step1Chunk5_2_checked, root8Node100Step1Chunk5_3_checked, root8Node100Step1Chunk5_4_checked, root8Node100Step1Chunk5_5_checked, root8Node100Step1Chunk6_0_checked, root8Node100Step1Chunk6_1_checked, root8Node100Step1Chunk6_2_checked, root8Node100Step1Chunk6_3_checked, root8Node100Step1Chunk6_4_checked, root8Node100Step1Chunk6_5_checked, root8Node100Step1Chunk7_0_checked, root8Node100Step1Chunk7_1_checked, root8Node100Step1Chunk7_2_checked, root8Node100Step1Chunk7_3_checked, root8Node100Step1Chunk7_4_checked, root8Node100Step1Chunk7_5_checked, root8Node100Step1Chunk8_0_checked, root8Node100Step1Chunk8_1_checked, root8Node100Step1Chunk8_2_checked, root8Node100Step1Chunk8_3_checked, root8Node100Step1Chunk8_4_checked, root8Node100Step1Chunk8_5_checked, Bool.true_and])
theorem root8Node100Step1_checked :
    checkReplacement table27 root8Node100Domains0 root8Node100Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root8Node100Domains0 root8Node100Domains1
    root8Node100Domains0Fast root8Node100Domains1Fast
    root8Node100Domains0_fast_eq root8Node100Domains1_fast_eq
    root8Node100Step1Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
