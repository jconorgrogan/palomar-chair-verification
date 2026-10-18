module

public import SpectreFinite.RadiusFiveRoot0Part36
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable1
public import SpectreFinite.RadiusFiveTable44
public import SpectreFinite.RadiusFiveTable51
public import SpectreFinite.RadiusFiveTable56

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node86Domains0 : Domains 91 State := restrict root0Node74Domains2 3 (6,4)
def root0Node86Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2),(7,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5),(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(1,5),(3,5),(7,5)]
  | 10 => some [(0,3),(6,1)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5),(6,3)]
  | 14 => some [(4,4),(7,2)]
  | 15 => some [(1,4),(7,4)]
  | 16 => some [(0,5),(6,3)]
  | 17 => some [(2,0),(2,2),(2,4)]
  | 18 => some [(1,3),(3,3),(7,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1)]
  | 26 => some [(0,1),(6,5)]
  | 27 => some [(0,4),(6,2)]
  | 28 => some [(5,4),(8,4)]
  | 29 => some [(1,4),(6,4)]
  | 30 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2),(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0),(7,0)]
  | 37 => some [(4,3),(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(0,3),(6,0)]
  | 40 => some [(0,3),(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(7,3)]
  | 49 => some [(4,2),(8,2)]
  | 50 => some [(5,0),(5,3),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1),(8,1)]
  | 58 => some [(0,1),(6,5)]
  | 59 => some [(0,4),(6,2)]
  | 60 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 79 => some [(0,2),(1,5),(6,0)]
  | 80 => some [(1,1),(6,1),(7,1)]
  | 81 => some [(4,1),(7,5),(8,1)]
  | 82 => some [(0,2),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => some [(2,0),(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,2)]
  | 89 => some [(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node86Domains0_fast_eq : root0Node86Domains0 = expandDomains root0Node86Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node86Domains0 v = expandDomains root0Node86Domains0Fast v from by decide) v
def root0Node86Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5),(8,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(3,5),(7,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5),(6,3)]
  | 14 => [(4,4),(7,2)]
  | 15 => [(1,4),(7,4)]
  | 16 => [(0,5),(6,3)]
  | 17 => [(2,2),(2,4)]
  | 18 => [(1,3),(3,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(0,2),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(7,5)]
  | 24 => [(0,2),(6,0)]
  | 25 => [(1,1),(7,1)]
  | 26 => [(0,1),(6,5)]
  | 27 => [(0,4),(6,2)]
  | 28 => [(5,4),(8,4)]
  | 29 => [(1,4),(6,4)]
  | 30 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => [(4,0),(8,0)]
  | 32 => [(7,3)]
  | 33 => [(5,2),(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(1,0),(7,0)]
  | 37 => [(4,3),(7,1)]
  | 38 => [(7,5)]
  | 39 => [(0,3),(6,0)]
  | 40 => [(0,3),(0,4),(6,1),(6,2)]
  | 41 => [(5,1),(5,4),(8,4)]
  | 42 => [(0,1),(6,4)]
  | 43 => [(1,2),(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(4,0),(7,4)]
  | 48 => [(1,3),(7,3)]
  | 49 => [(4,2),(8,2)]
  | 50 => [(5,0),(5,3),(8,0)]
  | 51 => [(4,3),(5,3),(7,1),(8,3)]
  | 52 => [(7,5),(8,5)]
  | 53 => [(0,3),(1,0)]
  | 54 => [(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(5,1),(8,1)]
  | 58 => [(0,1),(6,5)]
  | 59 => [(0,4),(6,2)]
  | 60 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 61 => [(1,3),(7,3)]
  | 62 => [(4,2),(8,2)]
  | 63 => [(5,0),(5,3)]
  | 64 => [(4,5),(5,5),(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(5,5),(8,5)]
  | 68 => [(1,0),(3,0),(7,0)]
  | 69 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 70 => [(0,4),(1,2),(6,2)]
  | 71 => [(1,4),(3,4),(5,4),(7,4)]
  | 72 => [(0,0),(0,5),(6,3)]
  | 73 => [(4,4),(7,2)]
  | 74 => [(1,4),(7,4)]
  | 75 => [(0,5),(1,3),(6,3)]
  | 76 => [(4,4),(7,2),(8,2)]
  | 77 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 79 => [(0,2),(1,5),(6,0)]
  | 80 => [(1,1),(6,1),(7,1)]
  | 81 => [(4,1),(7,5),(8,1)]
  | 82 => [(0,2),(6,0),(6,5)]
  | 83 => [(0,4),(1,1),(7,1)]
  | 84 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => [(2,0),(4,0),(8,0)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(8,2)]
  | 89 => [(5,0),(7,0),(8,0)]
  | _ => [(4,3),(4,5),(7,3),(8,3)]
def root0Node86Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5),(8,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5),(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5),(6,3)]
  | 14 => some [(4,4),(7,2)]
  | 15 => some [(1,4),(7,4)]
  | 16 => some [(0,5),(6,3)]
  | 17 => some [(2,2),(2,4)]
  | 18 => some [(1,3),(3,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(6,0)]
  | 25 => some [(1,1),(7,1)]
  | 26 => some [(0,1),(6,5)]
  | 27 => some [(0,4),(6,2)]
  | 28 => some [(5,4),(8,4)]
  | 29 => some [(1,4),(6,4)]
  | 30 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2),(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0),(7,0)]
  | 37 => some [(4,3),(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(0,3),(6,0)]
  | 40 => some [(0,3),(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(7,3)]
  | 49 => some [(4,2),(8,2)]
  | 50 => some [(5,0),(5,3),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1),(8,1)]
  | 58 => some [(0,1),(6,5)]
  | 59 => some [(0,4),(6,2)]
  | 60 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 79 => some [(0,2),(1,5),(6,0)]
  | 80 => some [(1,1),(6,1),(7,1)]
  | 81 => some [(4,1),(7,5),(8,1)]
  | 82 => some [(0,2),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => some [(2,0),(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,2)]
  | 89 => some [(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node86Domains1_fast_eq : root0Node86Domains1 = expandDomains root0Node86Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node86Domains1 v = expandDomains root0Node86Domains1Fast v from by decide) v
theorem root0Node86Step1Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq (by decide)
theorem root0Node86Step1Narrowing_checked :
    checkNarrowing table1 root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkNarrowing_flatten table1Scope [table1Rows0_0,table1Rows0_1,table1Rows0_2,table1Rows0_3,table1Rows0_4,table1Rows0_5,table1Rows1_0,table1Rows1_1,table1Rows1_2,table1Rows1_3,table1Rows1_4,table1Rows1_5,table1Rows2_0,table1Rows2_1,table1Rows2_2,table1Rows2_3,table1Rows2_4,table1Rows2_5,table1Rows3_0,table1Rows3_1,table1Rows3_2,table1Rows3_3,table1Rows3_4,table1Rows3_5,table1Rows4_0,table1Rows4_1,table1Rows4_2,table1Rows4_3,table1Rows4_4,table1Rows4_5,table1Rows5_0,table1Rows5_1,table1Rows5_2,table1Rows5_3,table1Rows5_4,table1Rows5_5,table1Rows6_0,table1Rows6_1,table1Rows6_2,table1Rows6_3,table1Rows6_4,table1Rows6_5,table1Rows7_0,table1Rows7_1,table1Rows7_2,table1Rows7_3,table1Rows7_4,table1Rows7_5,table1Rows8_0,table1Rows8_1,table1Rows8_2,table1Rows8_3,table1Rows8_4,table1Rows8_5]
    root0Node86Domains0 root0Node86Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node86Step1Chunk0_0_checked, root0Node86Step1Chunk0_1_checked, root0Node86Step1Chunk0_2_checked, root0Node86Step1Chunk0_3_checked, root0Node86Step1Chunk0_4_checked, root0Node86Step1Chunk0_5_checked, root0Node86Step1Chunk1_0_checked, root0Node86Step1Chunk1_1_checked, root0Node86Step1Chunk1_2_checked, root0Node86Step1Chunk1_3_checked, root0Node86Step1Chunk1_4_checked, root0Node86Step1Chunk1_5_checked, root0Node86Step1Chunk2_0_checked, root0Node86Step1Chunk2_1_checked, root0Node86Step1Chunk2_2_checked, root0Node86Step1Chunk2_3_checked, root0Node86Step1Chunk2_4_checked, root0Node86Step1Chunk2_5_checked, root0Node86Step1Chunk3_0_checked, root0Node86Step1Chunk3_1_checked, root0Node86Step1Chunk3_2_checked, root0Node86Step1Chunk3_3_checked, root0Node86Step1Chunk3_4_checked, root0Node86Step1Chunk3_5_checked, root0Node86Step1Chunk4_0_checked, root0Node86Step1Chunk4_1_checked, root0Node86Step1Chunk4_2_checked, root0Node86Step1Chunk4_3_checked, root0Node86Step1Chunk4_4_checked, root0Node86Step1Chunk4_5_checked, root0Node86Step1Chunk5_0_checked, root0Node86Step1Chunk5_1_checked, root0Node86Step1Chunk5_2_checked, root0Node86Step1Chunk5_3_checked, root0Node86Step1Chunk5_4_checked, root0Node86Step1Chunk5_5_checked, root0Node86Step1Chunk6_0_checked, root0Node86Step1Chunk6_1_checked, root0Node86Step1Chunk6_2_checked, root0Node86Step1Chunk6_3_checked, root0Node86Step1Chunk6_4_checked, root0Node86Step1Chunk6_5_checked, root0Node86Step1Chunk7_0_checked, root0Node86Step1Chunk7_1_checked, root0Node86Step1Chunk7_2_checked, root0Node86Step1Chunk7_3_checked, root0Node86Step1Chunk7_4_checked, root0Node86Step1Chunk7_5_checked, root0Node86Step1Chunk8_0_checked, root0Node86Step1Chunk8_1_checked, root0Node86Step1Chunk8_2_checked, root0Node86Step1Chunk8_3_checked, root0Node86Step1Chunk8_4_checked, root0Node86Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node86Step1_checked :
    checkReplacement table1 root0Node86Domains0 root0Node86Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node86Domains0 root0Node86Domains1
    root0Node86Domains0Fast root0Node86Domains1Fast
    root0Node86Domains0_fast_eq root0Node86Domains1_fast_eq
    root0Node86Step1Narrowing_checked (by decide)
def root0Node87Domains0 : Domains 91 State := restrict root0Node86Domains1 6 (5,5)
def root0Node87Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5),(7,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5),(6,3)]
  | 14 => some [(4,4),(7,2)]
  | 15 => some [(1,4),(7,4)]
  | 16 => some [(0,5),(6,3)]
  | 17 => some [(2,2),(2,4)]
  | 18 => some [(1,3),(3,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(6,0)]
  | 25 => some [(1,1),(7,1)]
  | 26 => some [(0,1),(6,5)]
  | 27 => some [(0,4),(6,2)]
  | 28 => some [(5,4),(8,4)]
  | 29 => some [(1,4),(6,4)]
  | 30 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(5,2),(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(1,0),(7,0)]
  | 37 => some [(4,3),(7,1)]
  | 38 => some [(7,5)]
  | 39 => some [(0,3),(6,0)]
  | 40 => some [(0,3),(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(4,0),(7,4)]
  | 48 => some [(1,3),(7,3)]
  | 49 => some [(4,2),(8,2)]
  | 50 => some [(5,0),(5,3),(8,0)]
  | 51 => some [(4,3),(5,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(5,1),(8,1)]
  | 58 => some [(0,1),(6,5)]
  | 59 => some [(0,4),(6,2)]
  | 60 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 70 => some [(0,4),(1,2),(6,2)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(1,3),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 79 => some [(0,2),(1,5),(6,0)]
  | 80 => some [(1,1),(6,1),(7,1)]
  | 81 => some [(4,1),(7,5),(8,1)]
  | 82 => some [(0,2),(6,0),(6,5)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => some [(2,0),(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,2)]
  | 89 => some [(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node87Domains0_fast_eq : root0Node87Domains0 = expandDomains root0Node87Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node87Domains0 v = expandDomains root0Node87Domains0Fast v from by decide) v
def root0Node87Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(3,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(2,4)]
  | 18 => [(1,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(6,5)]
  | 27 => [(0,4)]
  | 28 => [(5,4),(8,4)]
  | 29 => [(1,4),(6,4)]
  | 30 => [(7,2),(8,2)]
  | 31 => [(4,0),(8,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(7,5)]
  | 39 => [(0,3),(6,0)]
  | 40 => [(0,4),(6,1),(6,2)]
  | 41 => [(5,1),(5,4),(8,4)]
  | 42 => [(0,1),(6,4)]
  | 43 => [(1,2),(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(1,3)]
  | 49 => [(4,2),(8,2)]
  | 50 => [(5,0),(5,3),(8,0)]
  | 51 => [(4,3),(7,1),(8,3)]
  | 52 => [(7,5),(8,5)]
  | 53 => [(0,3),(1,0)]
  | 54 => [(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(8,1)]
  | 58 => [(6,5)]
  | 59 => [(0,4),(6,2)]
  | 60 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 61 => [(1,3),(7,3)]
  | 62 => [(4,2),(8,2)]
  | 63 => [(5,0),(5,3)]
  | 64 => [(4,5),(5,5),(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(5,5),(8,5)]
  | 68 => [(1,0),(3,0),(7,0)]
  | 69 => [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 70 => [(0,4),(6,2)]
  | 71 => [(1,4),(3,4),(5,4),(7,4)]
  | 72 => [(0,0),(0,5),(6,3)]
  | 73 => [(4,4),(7,2)]
  | 74 => [(1,4),(7,4)]
  | 75 => [(0,5),(6,3)]
  | 76 => [(4,4),(7,2),(8,2)]
  | 77 => [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => [(2,1),(2,3),(2,5),(4,3)]
  | 79 => [(0,2),(1,5),(6,0)]
  | 80 => [(1,1),(6,1),(7,1)]
  | 81 => [(4,1),(7,5)]
  | 82 => [(0,2),(6,0)]
  | 83 => [(0,4),(1,1),(7,1)]
  | 84 => [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => [(2,0),(4,0),(8,0)]
  | 87 => [(7,3),(8,3)]
  | 88 => [(5,2),(5,5),(8,2)]
  | 89 => [(5,0),(7,0),(8,0)]
  | _ => [(4,3),(4,5),(7,3),(8,3)]
def root0Node87Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,4)]
  | 18 => some [(1,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,5)]
  | 27 => some [(0,4)]
  | 28 => some [(5,4),(8,4)]
  | 29 => some [(1,4),(6,4)]
  | 30 => some [(7,2),(8,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(7,5)]
  | 39 => some [(0,3),(6,0)]
  | 40 => some [(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(4,2),(8,2)]
  | 50 => some [(5,0),(5,3),(8,0)]
  | 51 => some [(4,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4),(6,2)]
  | 60 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(1,0),(3,0),(7,0)]
  | 69 => some [(2,1),(2,3),(2,5),(4,3),(7,1)]
  | 70 => some [(0,4),(6,2)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(6,3)]
  | 76 => some [(4,4),(7,2),(8,2)]
  | 77 => some [(0,0),(1,4),(4,0),(5,0),(6,4),(7,4),(8,0)]
  | 78 => some [(2,1),(2,3),(2,5),(4,3)]
  | 79 => some [(0,2),(1,5),(6,0)]
  | 80 => some [(1,1),(6,1),(7,1)]
  | 81 => some [(4,1),(7,5)]
  | 82 => some [(0,2),(6,0)]
  | 83 => some [(0,4),(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => some [(2,0),(4,0),(8,0)]
  | 87 => some [(7,3),(8,3)]
  | 88 => some [(5,2),(5,5),(8,2)]
  | 89 => some [(5,0),(7,0),(8,0)]
  | _ => some [(4,3),(4,5),(7,3),(8,3)]
theorem root0Node87Domains1_fast_eq : root0Node87Domains1 = expandDomains root0Node87Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node87Domains1 v = expandDomains root0Node87Domains1Fast v from by decide) v
theorem root0Node87Step1Chunk0_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_0⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk0_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_1⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk0_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_2⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk0_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_3⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk0_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_4⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk0_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows0_5⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk1_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_0⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk1_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_1⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk1_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_2⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk1_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_3⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk1_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_4⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk1_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows1_5⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk2_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_0⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk2_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_1⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk2_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_2⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk2_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_3⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk2_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_4⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk2_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows2_5⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk3_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_0⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk3_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_1⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk3_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_2⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk3_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_3⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk3_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_4⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk3_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows3_5⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk4_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_0⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk4_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_1⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk4_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_2⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk4_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_3⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk4_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_4⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk4_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows4_5⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk5_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_0⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk5_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_1⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk5_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_2⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk5_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_3⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk5_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_4⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk5_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows5_5⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk6_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_0⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk6_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_1⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk6_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_2⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk6_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_3⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk6_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_4⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk6_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows6_5⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk7_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_0⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk7_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_1⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk7_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_2⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk7_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_3⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk7_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_4⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk7_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows7_5⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk8_0_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_0⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk8_1_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_1⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk8_2_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_2⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk8_3_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_3⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk8_4_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_4⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Chunk8_5_checked :
    checkNarrowing ⟨table44Scope, table44Rows8_5⟩
      root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq (by decide)
theorem root0Node87Step1Narrowing_checked :
    checkNarrowing table44 root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkNarrowing_flatten table44Scope [table44Rows0_0,table44Rows0_1,table44Rows0_2,table44Rows0_3,table44Rows0_4,table44Rows0_5,table44Rows1_0,table44Rows1_1,table44Rows1_2,table44Rows1_3,table44Rows1_4,table44Rows1_5,table44Rows2_0,table44Rows2_1,table44Rows2_2,table44Rows2_3,table44Rows2_4,table44Rows2_5,table44Rows3_0,table44Rows3_1,table44Rows3_2,table44Rows3_3,table44Rows3_4,table44Rows3_5,table44Rows4_0,table44Rows4_1,table44Rows4_2,table44Rows4_3,table44Rows4_4,table44Rows4_5,table44Rows5_0,table44Rows5_1,table44Rows5_2,table44Rows5_3,table44Rows5_4,table44Rows5_5,table44Rows6_0,table44Rows6_1,table44Rows6_2,table44Rows6_3,table44Rows6_4,table44Rows6_5,table44Rows7_0,table44Rows7_1,table44Rows7_2,table44Rows7_3,table44Rows7_4,table44Rows7_5,table44Rows8_0,table44Rows8_1,table44Rows8_2,table44Rows8_3,table44Rows8_4,table44Rows8_5]
    root0Node87Domains0 root0Node87Domains1 (by
      simp only [List.all_cons, List.all_nil, root0Node87Step1Chunk0_0_checked, root0Node87Step1Chunk0_1_checked, root0Node87Step1Chunk0_2_checked, root0Node87Step1Chunk0_3_checked, root0Node87Step1Chunk0_4_checked, root0Node87Step1Chunk0_5_checked, root0Node87Step1Chunk1_0_checked, root0Node87Step1Chunk1_1_checked, root0Node87Step1Chunk1_2_checked, root0Node87Step1Chunk1_3_checked, root0Node87Step1Chunk1_4_checked, root0Node87Step1Chunk1_5_checked, root0Node87Step1Chunk2_0_checked, root0Node87Step1Chunk2_1_checked, root0Node87Step1Chunk2_2_checked, root0Node87Step1Chunk2_3_checked, root0Node87Step1Chunk2_4_checked, root0Node87Step1Chunk2_5_checked, root0Node87Step1Chunk3_0_checked, root0Node87Step1Chunk3_1_checked, root0Node87Step1Chunk3_2_checked, root0Node87Step1Chunk3_3_checked, root0Node87Step1Chunk3_4_checked, root0Node87Step1Chunk3_5_checked, root0Node87Step1Chunk4_0_checked, root0Node87Step1Chunk4_1_checked, root0Node87Step1Chunk4_2_checked, root0Node87Step1Chunk4_3_checked, root0Node87Step1Chunk4_4_checked, root0Node87Step1Chunk4_5_checked, root0Node87Step1Chunk5_0_checked, root0Node87Step1Chunk5_1_checked, root0Node87Step1Chunk5_2_checked, root0Node87Step1Chunk5_3_checked, root0Node87Step1Chunk5_4_checked, root0Node87Step1Chunk5_5_checked, root0Node87Step1Chunk6_0_checked, root0Node87Step1Chunk6_1_checked, root0Node87Step1Chunk6_2_checked, root0Node87Step1Chunk6_3_checked, root0Node87Step1Chunk6_4_checked, root0Node87Step1Chunk6_5_checked, root0Node87Step1Chunk7_0_checked, root0Node87Step1Chunk7_1_checked, root0Node87Step1Chunk7_2_checked, root0Node87Step1Chunk7_3_checked, root0Node87Step1Chunk7_4_checked, root0Node87Step1Chunk7_5_checked, root0Node87Step1Chunk8_0_checked, root0Node87Step1Chunk8_1_checked, root0Node87Step1Chunk8_2_checked, root0Node87Step1Chunk8_3_checked, root0Node87Step1Chunk8_4_checked, root0Node87Step1Chunk8_5_checked, Bool.true_and])
theorem root0Node87Step1_checked :
    checkReplacement table44 root0Node87Domains0 root0Node87Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root0Node87Domains0 root0Node87Domains1
    root0Node87Domains0Fast root0Node87Domains1Fast
    root0Node87Domains0_fast_eq root0Node87Domains1_fast_eq
    root0Node87Step1Narrowing_checked (by decide)
def root0Node87Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(3,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(2,4)]
  | 18 => [(1,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(6,5)]
  | 27 => [(0,4)]
  | 28 => [(5,4)]
  | 29 => [(1,4),(6,4)]
  | 30 => [(7,2),(8,2)]
  | 31 => [(4,0),(8,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(7,5)]
  | 39 => [(0,3),(6,0)]
  | 40 => [(0,4),(6,1),(6,2)]
  | 41 => [(5,1),(5,4),(8,4)]
  | 42 => [(0,1),(6,4)]
  | 43 => [(1,2),(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(1,3)]
  | 49 => [(4,2),(8,2)]
  | 50 => [(5,0),(5,3),(8,0)]
  | 51 => [(4,3),(7,1),(8,3)]
  | 52 => [(7,5),(8,5)]
  | 53 => [(0,3),(1,0)]
  | 54 => [(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(8,1)]
  | 58 => [(6,5)]
  | 59 => [(0,4)]
  | 60 => [(1,4),(3,4),(5,4)]
  | 61 => [(1,3),(7,3)]
  | 62 => [(4,2),(8,2)]
  | 63 => [(5,0),(5,3)]
  | 64 => [(4,5),(5,5),(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(5,5),(8,5)]
  | 68 => [(3,0),(7,0)]
  | 69 => [(2,3),(2,5),(4,3)]
  | 70 => [(0,4),(6,2)]
  | 71 => [(1,4),(3,4),(5,4),(7,4)]
  | 72 => [(0,0),(0,5),(6,3)]
  | 73 => [(4,4),(7,2)]
  | 74 => [(1,4),(7,4)]
  | 75 => [(0,5),(6,3)]
  | 76 => [(4,4),(7,2)]
  | 77 => [(0,0),(1,4),(6,4),(7,4)]
  | 78 => [(2,1),(2,3),(2,5),(4,3)]
  | 79 => [(0,2),(1,5),(6,0)]
  | 80 => [(1,1),(6,1),(7,1)]
  | 81 => [(4,1),(7,5)]
  | 82 => [(0,2),(6,0)]
  | 83 => [(1,1),(7,1)]
  | 84 => [(1,5),(4,1),(7,5),(8,1)]
  | 85 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => [(2,0),(4,0)]
  | 87 => [(7,3)]
  | 88 => [(5,2),(8,2)]
  | 89 => [(5,0),(8,0)]
  | _ => [(4,5),(7,3),(8,3)]
def root0Node87Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,4)]
  | 18 => some [(1,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,5)]
  | 27 => some [(0,4)]
  | 28 => some [(5,4)]
  | 29 => some [(1,4),(6,4)]
  | 30 => some [(7,2),(8,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(7,5)]
  | 39 => some [(0,3),(6,0)]
  | 40 => some [(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(4,2),(8,2)]
  | 50 => some [(5,0),(5,3),(8,0)]
  | 51 => some [(4,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(1,4),(3,4),(5,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(3,0),(7,0)]
  | 69 => some [(2,3),(2,5),(4,3)]
  | 70 => some [(0,4),(6,2)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(6,3)]
  | 76 => some [(4,4),(7,2)]
  | 77 => some [(0,0),(1,4),(6,4),(7,4)]
  | 78 => some [(2,1),(2,3),(2,5),(4,3)]
  | 79 => some [(0,2),(1,5),(6,0)]
  | 80 => some [(1,1),(6,1),(7,1)]
  | 81 => some [(4,1),(7,5)]
  | 82 => some [(0,2),(6,0)]
  | 83 => some [(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 86 => some [(2,0),(4,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2),(8,2)]
  | 89 => some [(5,0),(8,0)]
  | _ => some [(4,5),(7,3),(8,3)]
theorem root0Node87Domains2_fast_eq : root0Node87Domains2 = expandDomains root0Node87Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node87Domains2 v = expandDomains root0Node87Domains2Fast v from by decide) v
theorem root0Node87Step2Chunk0_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_0⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk0_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_1⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk0_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_2⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk0_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_3⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk0_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_4⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk0_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows0_5⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk1_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_0⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk1_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_1⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk1_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_2⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk1_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_3⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk1_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_4⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk1_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows1_5⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk2_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_0⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk2_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_1⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk2_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_2⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk2_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_3⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk2_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_4⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk2_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows2_5⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk3_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_0⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk3_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_1⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk3_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_2⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk3_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_3⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk3_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_4⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk3_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows3_5⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk4_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_0⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk4_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_1⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk4_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_2⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk4_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_3⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk4_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_4⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk4_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows4_5⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk5_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_0⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk5_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_1⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk5_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_2⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk5_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_3⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk5_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_4⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk5_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows5_5⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk6_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_0⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk6_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_1⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk6_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_2⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk6_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_3⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk6_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_4⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk6_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows6_5⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk7_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_0⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk7_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_1⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk7_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_2⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk7_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_3⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk7_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_4⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk7_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows7_5⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk8_0_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_0⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk8_1_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_1⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk8_2_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_2⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk8_3_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_3⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk8_4_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_4⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Chunk8_5_checked :
    checkNarrowing ⟨table56Scope, table56Rows8_5⟩
      root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq (by decide)
theorem root0Node87Step2Narrowing_checked :
    checkNarrowing table56 root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkNarrowing_flatten table56Scope [table56Rows0_0,table56Rows0_1,table56Rows0_2,table56Rows0_3,table56Rows0_4,table56Rows0_5,table56Rows1_0,table56Rows1_1,table56Rows1_2,table56Rows1_3,table56Rows1_4,table56Rows1_5,table56Rows2_0,table56Rows2_1,table56Rows2_2,table56Rows2_3,table56Rows2_4,table56Rows2_5,table56Rows3_0,table56Rows3_1,table56Rows3_2,table56Rows3_3,table56Rows3_4,table56Rows3_5,table56Rows4_0,table56Rows4_1,table56Rows4_2,table56Rows4_3,table56Rows4_4,table56Rows4_5,table56Rows5_0,table56Rows5_1,table56Rows5_2,table56Rows5_3,table56Rows5_4,table56Rows5_5,table56Rows6_0,table56Rows6_1,table56Rows6_2,table56Rows6_3,table56Rows6_4,table56Rows6_5,table56Rows7_0,table56Rows7_1,table56Rows7_2,table56Rows7_3,table56Rows7_4,table56Rows7_5,table56Rows8_0,table56Rows8_1,table56Rows8_2,table56Rows8_3,table56Rows8_4,table56Rows8_5]
    root0Node87Domains1 root0Node87Domains2 (by
      simp only [List.all_cons, List.all_nil, root0Node87Step2Chunk0_0_checked, root0Node87Step2Chunk0_1_checked, root0Node87Step2Chunk0_2_checked, root0Node87Step2Chunk0_3_checked, root0Node87Step2Chunk0_4_checked, root0Node87Step2Chunk0_5_checked, root0Node87Step2Chunk1_0_checked, root0Node87Step2Chunk1_1_checked, root0Node87Step2Chunk1_2_checked, root0Node87Step2Chunk1_3_checked, root0Node87Step2Chunk1_4_checked, root0Node87Step2Chunk1_5_checked, root0Node87Step2Chunk2_0_checked, root0Node87Step2Chunk2_1_checked, root0Node87Step2Chunk2_2_checked, root0Node87Step2Chunk2_3_checked, root0Node87Step2Chunk2_4_checked, root0Node87Step2Chunk2_5_checked, root0Node87Step2Chunk3_0_checked, root0Node87Step2Chunk3_1_checked, root0Node87Step2Chunk3_2_checked, root0Node87Step2Chunk3_3_checked, root0Node87Step2Chunk3_4_checked, root0Node87Step2Chunk3_5_checked, root0Node87Step2Chunk4_0_checked, root0Node87Step2Chunk4_1_checked, root0Node87Step2Chunk4_2_checked, root0Node87Step2Chunk4_3_checked, root0Node87Step2Chunk4_4_checked, root0Node87Step2Chunk4_5_checked, root0Node87Step2Chunk5_0_checked, root0Node87Step2Chunk5_1_checked, root0Node87Step2Chunk5_2_checked, root0Node87Step2Chunk5_3_checked, root0Node87Step2Chunk5_4_checked, root0Node87Step2Chunk5_5_checked, root0Node87Step2Chunk6_0_checked, root0Node87Step2Chunk6_1_checked, root0Node87Step2Chunk6_2_checked, root0Node87Step2Chunk6_3_checked, root0Node87Step2Chunk6_4_checked, root0Node87Step2Chunk6_5_checked, root0Node87Step2Chunk7_0_checked, root0Node87Step2Chunk7_1_checked, root0Node87Step2Chunk7_2_checked, root0Node87Step2Chunk7_3_checked, root0Node87Step2Chunk7_4_checked, root0Node87Step2Chunk7_5_checked, root0Node87Step2Chunk8_0_checked, root0Node87Step2Chunk8_1_checked, root0Node87Step2Chunk8_2_checked, root0Node87Step2Chunk8_3_checked, root0Node87Step2Chunk8_4_checked, root0Node87Step2Chunk8_5_checked, Bool.true_and])
theorem root0Node87Step2_checked :
    checkReplacement table56 root0Node87Domains1 root0Node87Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root0Node87Domains1 root0Node87Domains2
    root0Node87Domains1Fast root0Node87Domains2Fast
    root0Node87Domains1_fast_eq root0Node87Domains2_fast_eq
    root0Node87Step2Narrowing_checked (by decide)
def root0Node87Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(7,4)]
  | 6 => [(5,5)]
  | 7 => [(7,0)]
  | 8 => [(4,3)]
  | 9 => [(3,5)]
  | 10 => [(0,3)]
  | 11 => [(4,1)]
  | 12 => [(0,2)]
  | 13 => [(0,5)]
  | 14 => [(4,4)]
  | 15 => [(1,4)]
  | 16 => [(0,5)]
  | 17 => [(2,4)]
  | 18 => [(1,3)]
  | 19 => [(5,2)]
  | 20 => [(8,0)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(6,5)]
  | 27 => [(0,4)]
  | 28 => [(5,4)]
  | 29 => [(1,4),(6,4)]
  | 30 => [(7,2),(8,2)]
  | 31 => [(4,0),(8,0)]
  | 32 => [(7,3)]
  | 33 => [(8,2)]
  | 34 => [(5,0)]
  | 35 => [(4,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(7,5)]
  | 39 => [(0,3),(6,0)]
  | 40 => [(0,4),(6,1),(6,2)]
  | 41 => [(5,1),(5,4),(8,4)]
  | 42 => [(0,1),(6,4)]
  | 43 => [(1,2),(6,2)]
  | 44 => [(8,4)]
  | 45 => [(0,0)]
  | 46 => [(7,2)]
  | 47 => [(7,4)]
  | 48 => [(1,3)]
  | 49 => [(4,2),(8,2)]
  | 50 => [(5,0),(5,3),(8,0)]
  | 51 => [(4,3),(7,1),(8,3)]
  | 52 => [(7,5),(8,5)]
  | 53 => [(0,3),(1,0)]
  | 54 => [(7,1),(8,1)]
  | 55 => [(1,5)]
  | 56 => [(6,1)]
  | 57 => [(8,1)]
  | 58 => [(6,5)]
  | 59 => [(0,4)]
  | 60 => [(1,4),(3,4),(5,4)]
  | 61 => [(1,3),(7,3)]
  | 62 => [(4,2),(8,2)]
  | 63 => [(5,0),(5,3)]
  | 64 => [(4,5),(5,5),(8,5)]
  | 65 => [(7,0)]
  | 66 => [(8,3)]
  | 67 => [(5,5),(8,5)]
  | 68 => [(3,0),(7,0)]
  | 69 => [(2,3),(2,5),(4,3)]
  | 70 => [(0,4),(6,2)]
  | 71 => [(1,4),(3,4),(5,4),(7,4)]
  | 72 => [(0,0),(0,5),(6,3)]
  | 73 => [(4,4),(7,2)]
  | 74 => [(1,4),(7,4)]
  | 75 => [(0,5),(6,3)]
  | 76 => [(4,4),(7,2)]
  | 77 => [(0,0),(1,4),(6,4),(7,4)]
  | 78 => [(2,1),(2,3),(2,5),(4,3)]
  | 79 => [(0,2),(1,5),(6,0)]
  | 80 => [(1,1),(6,1),(7,1)]
  | 81 => [(4,1),(7,5)]
  | 82 => [(0,2),(6,0)]
  | 83 => [(1,1),(7,1)]
  | 84 => [(1,5),(4,1),(7,5),(8,1)]
  | 85 => [(0,5),(1,2),(3,2),(7,2)]
  | 86 => [(2,0),(4,0)]
  | 87 => [(7,3)]
  | 88 => [(5,2),(8,2)]
  | 89 => [(5,0),(8,0)]
  | _ => [(4,5),(7,3),(8,3)]
def root0Node87Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(7,4)]
  | 6 => some [(5,5)]
  | 7 => some [(7,0)]
  | 8 => some [(4,3)]
  | 9 => some [(3,5)]
  | 10 => some [(0,3)]
  | 11 => some [(4,1)]
  | 12 => some [(0,2)]
  | 13 => some [(0,5)]
  | 14 => some [(4,4)]
  | 15 => some [(1,4)]
  | 16 => some [(0,5)]
  | 17 => some [(2,4)]
  | 18 => some [(1,3)]
  | 19 => some [(5,2)]
  | 20 => some [(8,0)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,5)]
  | 27 => some [(0,4)]
  | 28 => some [(5,4)]
  | 29 => some [(1,4),(6,4)]
  | 30 => some [(7,2),(8,2)]
  | 31 => some [(4,0),(8,0)]
  | 32 => some [(7,3)]
  | 33 => some [(8,2)]
  | 34 => some [(5,0)]
  | 35 => some [(4,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(7,5)]
  | 39 => some [(0,3),(6,0)]
  | 40 => some [(0,4),(6,1),(6,2)]
  | 41 => some [(5,1),(5,4),(8,4)]
  | 42 => some [(0,1),(6,4)]
  | 43 => some [(1,2),(6,2)]
  | 44 => some [(8,4)]
  | 45 => some [(0,0)]
  | 46 => some [(7,2)]
  | 47 => some [(7,4)]
  | 48 => some [(1,3)]
  | 49 => some [(4,2),(8,2)]
  | 50 => some [(5,0),(5,3),(8,0)]
  | 51 => some [(4,3),(7,1),(8,3)]
  | 52 => some [(7,5),(8,5)]
  | 53 => some [(0,3),(1,0)]
  | 54 => some [(7,1),(8,1)]
  | 55 => some [(1,5)]
  | 56 => some [(6,1)]
  | 57 => some [(8,1)]
  | 58 => some [(6,5)]
  | 59 => some [(0,4)]
  | 60 => some [(1,4),(3,4),(5,4)]
  | 61 => some [(1,3),(7,3)]
  | 62 => some [(4,2),(8,2)]
  | 63 => some [(5,0),(5,3)]
  | 64 => some [(4,5),(5,5),(8,5)]
  | 65 => some [(7,0)]
  | 66 => some [(8,3)]
  | 67 => some [(5,5),(8,5)]
  | 68 => some [(3,0),(7,0)]
  | 69 => some [(2,3),(2,5),(4,3)]
  | 70 => some [(0,4),(6,2)]
  | 71 => some [(1,4),(3,4),(5,4),(7,4)]
  | 72 => some [(0,0),(0,5),(6,3)]
  | 73 => some [(4,4),(7,2)]
  | 74 => some [(1,4),(7,4)]
  | 75 => some [(0,5),(6,3)]
  | 76 => some [(4,4),(7,2)]
  | 77 => some [(0,0),(1,4),(6,4),(7,4)]
  | 78 => some [(2,1),(2,3),(2,5),(4,3)]
  | 79 => some [(0,2),(1,5),(6,0)]
  | 80 => some [(1,1),(6,1),(7,1)]
  | 81 => some [(4,1),(7,5)]
  | 82 => some [(0,2),(6,0)]
  | 83 => some [(1,1),(7,1)]
  | 84 => some [(1,5),(4,1),(7,5),(8,1)]
  | 85 => some [(0,5),(1,2),(3,2),(7,2)]
  | 86 => some [(2,0),(4,0)]
  | 87 => some [(7,3)]
  | 88 => some [(5,2),(8,2)]
  | 89 => some [(5,0),(8,0)]
  | _ => some [(4,5),(7,3),(8,3)]
theorem root0Node87Domains3_fast_eq : root0Node87Domains3 = expandDomains root0Node87Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root0Node87Domains3 v = expandDomains root0Node87Domains3Fast v from by decide) v
theorem root0Node87Step3Chunk0_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_0⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk0_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_1⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk0_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_2⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk0_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_3⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk0_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_4⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk0_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows0_5⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk1_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_0⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk1_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_1⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk1_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_2⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk1_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_3⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk1_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_4⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk1_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows1_5⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk2_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_0⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk2_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_1⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk2_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_2⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk2_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_3⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk2_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_4⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk2_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows2_5⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk3_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_0⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk3_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_1⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk3_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_2⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk3_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_3⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk3_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_4⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk3_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows3_5⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk4_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_0⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk4_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_1⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk4_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_2⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk4_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_3⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk4_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_4⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk4_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows4_5⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk5_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_0⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk5_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_1⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk5_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_2⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk5_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_3⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk5_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_4⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk5_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows5_5⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk6_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_0⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk6_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_1⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk6_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_2⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk6_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_3⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk6_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_4⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk6_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows6_5⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk7_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_0⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk7_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_1⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk7_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_2⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk7_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_3⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk7_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_4⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk7_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows7_5⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk8_0_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_0⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk8_1_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_1⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk8_2_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_2⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk8_3_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_3⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk8_4_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_4⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Chunk8_5_checked :
    checkNarrowing ⟨table51Scope, table51Rows8_5⟩
      root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq (by decide)
theorem root0Node87Step3Narrowing_checked :
    checkNarrowing table51 root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkNarrowing_flatten table51Scope [table51Rows0_0,table51Rows0_1,table51Rows0_2,table51Rows0_3,table51Rows0_4,table51Rows0_5,table51Rows1_0,table51Rows1_1,table51Rows1_2,table51Rows1_3,table51Rows1_4,table51Rows1_5,table51Rows2_0,table51Rows2_1,table51Rows2_2,table51Rows2_3,table51Rows2_4,table51Rows2_5,table51Rows3_0,table51Rows3_1,table51Rows3_2,table51Rows3_3,table51Rows3_4,table51Rows3_5,table51Rows4_0,table51Rows4_1,table51Rows4_2,table51Rows4_3,table51Rows4_4,table51Rows4_5,table51Rows5_0,table51Rows5_1,table51Rows5_2,table51Rows5_3,table51Rows5_4,table51Rows5_5,table51Rows6_0,table51Rows6_1,table51Rows6_2,table51Rows6_3,table51Rows6_4,table51Rows6_5,table51Rows7_0,table51Rows7_1,table51Rows7_2,table51Rows7_3,table51Rows7_4,table51Rows7_5,table51Rows8_0,table51Rows8_1,table51Rows8_2,table51Rows8_3,table51Rows8_4,table51Rows8_5]
    root0Node87Domains2 root0Node87Domains3 (by
      simp only [List.all_cons, List.all_nil, root0Node87Step3Chunk0_0_checked, root0Node87Step3Chunk0_1_checked, root0Node87Step3Chunk0_2_checked, root0Node87Step3Chunk0_3_checked, root0Node87Step3Chunk0_4_checked, root0Node87Step3Chunk0_5_checked, root0Node87Step3Chunk1_0_checked, root0Node87Step3Chunk1_1_checked, root0Node87Step3Chunk1_2_checked, root0Node87Step3Chunk1_3_checked, root0Node87Step3Chunk1_4_checked, root0Node87Step3Chunk1_5_checked, root0Node87Step3Chunk2_0_checked, root0Node87Step3Chunk2_1_checked, root0Node87Step3Chunk2_2_checked, root0Node87Step3Chunk2_3_checked, root0Node87Step3Chunk2_4_checked, root0Node87Step3Chunk2_5_checked, root0Node87Step3Chunk3_0_checked, root0Node87Step3Chunk3_1_checked, root0Node87Step3Chunk3_2_checked, root0Node87Step3Chunk3_3_checked, root0Node87Step3Chunk3_4_checked, root0Node87Step3Chunk3_5_checked, root0Node87Step3Chunk4_0_checked, root0Node87Step3Chunk4_1_checked, root0Node87Step3Chunk4_2_checked, root0Node87Step3Chunk4_3_checked, root0Node87Step3Chunk4_4_checked, root0Node87Step3Chunk4_5_checked, root0Node87Step3Chunk5_0_checked, root0Node87Step3Chunk5_1_checked, root0Node87Step3Chunk5_2_checked, root0Node87Step3Chunk5_3_checked, root0Node87Step3Chunk5_4_checked, root0Node87Step3Chunk5_5_checked, root0Node87Step3Chunk6_0_checked, root0Node87Step3Chunk6_1_checked, root0Node87Step3Chunk6_2_checked, root0Node87Step3Chunk6_3_checked, root0Node87Step3Chunk6_4_checked, root0Node87Step3Chunk6_5_checked, root0Node87Step3Chunk7_0_checked, root0Node87Step3Chunk7_1_checked, root0Node87Step3Chunk7_2_checked, root0Node87Step3Chunk7_3_checked, root0Node87Step3Chunk7_4_checked, root0Node87Step3Chunk7_5_checked, root0Node87Step3Chunk8_0_checked, root0Node87Step3Chunk8_1_checked, root0Node87Step3Chunk8_2_checked, root0Node87Step3Chunk8_3_checked, root0Node87Step3Chunk8_4_checked, root0Node87Step3Chunk8_5_checked, Bool.true_and])
theorem root0Node87Step3_checked :
    checkReplacement table51 root0Node87Domains2 root0Node87Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root0Node87Domains2 root0Node87Domains3
    root0Node87Domains2Fast root0Node87Domains3Fast
    root0Node87Domains2_fast_eq root0Node87Domains3_fast_eq
    root0Node87Step3Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
