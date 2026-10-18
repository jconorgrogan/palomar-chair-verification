module

public import SpectreFinite.RadiusFiveRoot1Part12
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFiveFastReplacement
public import SpectreFinite.RadiusFiveTable12
public import SpectreFinite.RadiusFiveTable13
public import SpectreFinite.RadiusFiveTable34
public import SpectreFinite.RadiusFiveTable65

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFive
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node35Domains0 : Domains 91 State := restrict root1Node1Domains3 0 (8,2)
def root1Node35Domains0Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0),(5,3),(8,0)]
  | 2 => some [(4,5),(7,3),(8,5)]
  | 3 => some [(4,2),(7,0)]
  | 4 => some [(4,3),(5,3),(8,3)]
  | 5 => some [(7,5),(8,5)]
  | 6 => some [(0,4),(6,2)]
  | 7 => some [(3,4),(5,4),(7,4)]
  | 8 => some [(0,0),(6,3),(6,4)]
  | 9 => some [(1,2),(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(2,2),(7,2)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(2,1),(2,3),(4,3)]
  | 15 => some [(0,2),(1,5),(7,5)]
  | 16 => some [(0,3),(1,1),(6,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(0,1),(4,1),(5,1),(8,1)]
  | 21 => some [(4,4),(7,2)]
  | 22 => some [(0,0),(1,4),(6,4),(7,4)]
  | 23 => some [(0,5),(1,2),(3,2),(6,3)]
  | 24 => some [(2,0),(2,2),(4,0)]
  | 25 => some [(3,3),(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(5,0),(8,0)]
  | 28 => some [(4,5),(7,3),(8,3)]
  | 29 => some [(1,0),(5,2),(5,5)]
  | 30 => some [(1,1),(7,1)]
  | 31 => some [(1,5),(4,1),(7,5)]
  | 32 => some [(0,2),(0,3),(6,0),(6,1)]
  | 33 => some [(1,1),(3,1),(5,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0),(1,4),(6,4)]
  | 38 => some [(0,5),(1,2),(7,2)]
  | 39 => some [(4,0),(4,4),(8,4)]
  | 40 => some [(4,0),(5,0),(8,0)]
  | 41 => some [(4,5),(7,3)]
  | 42 => some [(4,2),(5,2),(7,0),(8,2)]
  | 43 => some [(5,0),(5,3),(8,3)]
  | 44 => some [(4,5),(8,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(1,5),(7,5)]
  | 48 => some [(0,3),(6,0),(6,1)]
  | 49 => some [(5,1),(7,1),(8,1)]
  | 50 => some [(0,1),(1,5),(7,5)]
  | 51 => some [(0,0),(0,1),(6,4)]
  | 52 => some [(1,2),(6,2),(7,2)]
  | 53 => some [(7,4),(8,4)]
  | 54 => some [(0,0),(1,3),(6,3)]
  | 55 => some [(7,2),(8,2)]
  | 56 => some [(4,0),(5,0),(8,0)]
  | 57 => some [(4,5),(7,3)]
  | 58 => some [(4,2),(7,0),(8,2)]
  | 59 => some [(5,0),(5,3),(8,0),(8,3)]
  | 60 => some [(4,5),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0),(6,1)]
  | 62 => some [(4,1),(7,1),(8,1)]
  | 63 => some [(0,2),(1,5),(6,5)]
  | 64 => some [(0,4),(1,1),(6,1)]
  | 65 => some [(5,1),(5,4)]
  | 66 => some [(0,0),(0,1),(6,4)]
  | 67 => some [(1,2),(6,2),(7,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(6,3),(6,4)]
  | 70 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,3)]
  | 71 => some [(4,5),(5,2),(5,5),(8,5)]
  | 72 => some [(7,0),(8,0)]
  | 73 => some [(4,3),(8,3)]
  | 74 => some [(1,5),(3,5),(5,5),(7,5),(8,5)]
  | 75 => some [(0,3),(1,0),(6,1)]
  | 76 => some [(2,1),(4,1),(7,1),(8,1)]
  | 77 => some [(0,2),(1,5),(7,5)]
  | 78 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(5,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | 83 => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
  | 84 => some [(3,2),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 85 => some [(1,1),(4,3),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,4),(1,5),(3,4),(5,1),(5,4),(6,5)]
  | _ => some [(0,0),(0,1),(0,4),(0,5),(6,1),(6,2),(6,3),(6,4)]
theorem root1Node35Domains0_fast_eq : root1Node35Domains0 = expandDomains root1Node35Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node35Domains0 v = expandDomains root1Node35Domains0Fast v from by decide) v
def root1Node35Domains1 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0),(8,0)]
  | 2 => [(4,5),(7,3)]
  | 3 => [(4,2),(7,0)]
  | 4 => [(5,3),(8,3)]
  | 5 => [(7,5),(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(0,0),(6,4)]
  | 9 => [(1,2),(7,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(2,2),(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(1,5),(7,5)]
  | 16 => [(0,3),(6,1)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(0,1),(4,1),(5,1),(8,1)]
  | 21 => [(4,4),(7,2)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(2,0),(2,2)]
  | 25 => [(3,3),(7,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3),(8,3)]
  | 29 => [(1,0),(5,2),(5,5)]
  | 30 => [(1,1),(7,1)]
  | 31 => [(4,1),(7,5)]
  | 32 => [(0,2),(6,0)]
  | 33 => [(1,1),(3,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(1,4),(6,4)]
  | 38 => [(0,5),(1,2)]
  | 39 => [(4,0),(4,4),(8,4)]
  | 40 => [(4,0),(5,0),(8,0)]
  | 41 => [(7,3)]
  | 42 => [(5,2),(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3),(6,0)]
  | 49 => [(5,1),(7,1),(8,1)]
  | 50 => [(0,1),(1,5),(7,5)]
  | 51 => [(0,0),(0,1),(6,4)]
  | 52 => [(1,2),(6,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2),(8,2)]
  | 59 => [(5,0),(5,3),(8,0),(8,3)]
  | 60 => [(4,5),(7,3),(8,5)]
  | 61 => [(0,3),(1,0),(6,1)]
  | 62 => [(7,1),(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(7,4),(8,4)]
  | 69 => [(0,0),(6,3),(6,4)]
  | 70 => [(1,3),(3,3),(5,0),(5,3),(7,3),(8,3)]
  | 71 => [(4,5),(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5),(8,5)]
  | 75 => [(1,0)]
  | 76 => [(2,1),(4,1),(7,1),(8,1)]
  | 77 => [(0,2),(1,5),(7,5)]
  | 78 => [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 79 => [(4,4),(5,4),(7,2),(8,4)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3)]
  | 82 => [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | 83 => [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
  | 84 => [(3,2),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 85 => [(1,1),(4,3),(6,1),(7,1)]
  | 86 => [(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,5)]
  | 88 => [(0,4),(1,1),(3,1),(7,1)]
  | 89 => [(0,1),(1,4),(1,5),(3,4),(5,1),(5,4),(6,5)]
  | _ => [(0,0),(0,1),(0,4),(0,5),(6,1),(6,2),(6,3),(6,4)]
def root1Node35Domains1Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0),(8,0)]
  | 2 => some [(4,5),(7,3)]
  | 3 => some [(4,2),(7,0)]
  | 4 => some [(5,3),(8,3)]
  | 5 => some [(7,5),(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(0,0),(6,4)]
  | 9 => some [(1,2),(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(2,2),(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(1,5),(7,5)]
  | 16 => some [(0,3),(6,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(0,1),(4,1),(5,1),(8,1)]
  | 21 => some [(4,4),(7,2)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(2,0),(2,2)]
  | 25 => some [(3,3),(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3),(8,3)]
  | 29 => some [(1,0),(5,2),(5,5)]
  | 30 => some [(1,1),(7,1)]
  | 31 => some [(4,1),(7,5)]
  | 32 => some [(0,2),(6,0)]
  | 33 => some [(1,1),(3,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4),(6,4)]
  | 38 => some [(0,5),(1,2)]
  | 39 => some [(4,0),(4,4),(8,4)]
  | 40 => some [(4,0),(5,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(5,2),(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3),(6,0)]
  | 49 => some [(5,1),(7,1),(8,1)]
  | 50 => some [(0,1),(1,5),(7,5)]
  | 51 => some [(0,0),(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2),(8,2)]
  | 59 => some [(5,0),(5,3),(8,0),(8,3)]
  | 60 => some [(4,5),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0),(6,1)]
  | 62 => some [(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(6,3),(6,4)]
  | 70 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,3)]
  | 71 => some [(4,5),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(2,1),(4,1),(7,1),(8,1)]
  | 77 => some [(0,2),(1,5),(7,5)]
  | 78 => some [(0,0),(0,4),(0,5),(6,2),(6,3)]
  | 79 => some [(4,4),(5,4),(7,2),(8,4)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(2,0),(2,2),(2,4),(4,2),(4,4),(7,2),(8,2)]
  | 83 => some [(0,0),(1,3),(3,3),(4,0),(5,0),(5,3),(7,3),(8,0)]
  | 84 => some [(3,2),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 85 => some [(1,1),(4,3),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(3,1),(7,1)]
  | 89 => some [(0,1),(1,4),(1,5),(3,4),(5,1),(5,4),(6,5)]
  | _ => some [(0,0),(0,1),(0,4),(0,5),(6,1),(6,2),(6,3),(6,4)]
theorem root1Node35Domains1_fast_eq : root1Node35Domains1 = expandDomains root1Node35Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node35Domains1 v = expandDomains root1Node35Domains1Fast v from by decide) v
theorem root1Node35Step1Chunk0_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_0⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk0_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_1⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk0_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_2⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk0_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_3⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk0_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_4⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk0_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows0_5⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk1_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_0⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk1_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_1⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk1_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_2⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk1_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_3⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk1_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_4⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk1_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows1_5⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk2_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_0⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk2_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_1⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk2_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_2⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk2_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_3⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk2_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_4⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk2_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows2_5⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk3_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_0⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk3_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_1⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk3_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_2⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk3_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_3⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk3_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_4⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk3_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows3_5⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk4_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_0⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk4_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_1⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk4_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_2⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk4_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_3⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk4_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_4⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk4_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows4_5⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk5_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_0⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk5_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_1⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk5_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_2⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk5_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_3⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk5_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_4⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk5_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows5_5⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk6_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_0⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk6_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_1⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk6_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_2⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk6_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_3⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk6_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_4⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk6_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows6_5⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk7_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_0⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk7_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_1⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk7_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_2⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk7_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_3⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk7_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_4⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk7_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows7_5⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk8_0_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_0⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk8_1_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_1⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk8_2_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_2⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk8_3_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_3⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk8_4_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_4⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Chunk8_5_checked :
    checkNarrowing ⟨table34Scope, table34Rows8_5⟩
      root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq (by decide)
theorem root1Node35Step1Narrowing_checked :
    checkNarrowing table34 root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkNarrowing_flatten table34Scope [table34Rows0_0,table34Rows0_1,table34Rows0_2,table34Rows0_3,table34Rows0_4,table34Rows0_5,table34Rows1_0,table34Rows1_1,table34Rows1_2,table34Rows1_3,table34Rows1_4,table34Rows1_5,table34Rows2_0,table34Rows2_1,table34Rows2_2,table34Rows2_3,table34Rows2_4,table34Rows2_5,table34Rows3_0,table34Rows3_1,table34Rows3_2,table34Rows3_3,table34Rows3_4,table34Rows3_5,table34Rows4_0,table34Rows4_1,table34Rows4_2,table34Rows4_3,table34Rows4_4,table34Rows4_5,table34Rows5_0,table34Rows5_1,table34Rows5_2,table34Rows5_3,table34Rows5_4,table34Rows5_5,table34Rows6_0,table34Rows6_1,table34Rows6_2,table34Rows6_3,table34Rows6_4,table34Rows6_5,table34Rows7_0,table34Rows7_1,table34Rows7_2,table34Rows7_3,table34Rows7_4,table34Rows7_5,table34Rows8_0,table34Rows8_1,table34Rows8_2,table34Rows8_3,table34Rows8_4,table34Rows8_5]
    root1Node35Domains0 root1Node35Domains1 (by
      simp only [List.all_cons, List.all_nil, root1Node35Step1Chunk0_0_checked, root1Node35Step1Chunk0_1_checked, root1Node35Step1Chunk0_2_checked, root1Node35Step1Chunk0_3_checked, root1Node35Step1Chunk0_4_checked, root1Node35Step1Chunk0_5_checked, root1Node35Step1Chunk1_0_checked, root1Node35Step1Chunk1_1_checked, root1Node35Step1Chunk1_2_checked, root1Node35Step1Chunk1_3_checked, root1Node35Step1Chunk1_4_checked, root1Node35Step1Chunk1_5_checked, root1Node35Step1Chunk2_0_checked, root1Node35Step1Chunk2_1_checked, root1Node35Step1Chunk2_2_checked, root1Node35Step1Chunk2_3_checked, root1Node35Step1Chunk2_4_checked, root1Node35Step1Chunk2_5_checked, root1Node35Step1Chunk3_0_checked, root1Node35Step1Chunk3_1_checked, root1Node35Step1Chunk3_2_checked, root1Node35Step1Chunk3_3_checked, root1Node35Step1Chunk3_4_checked, root1Node35Step1Chunk3_5_checked, root1Node35Step1Chunk4_0_checked, root1Node35Step1Chunk4_1_checked, root1Node35Step1Chunk4_2_checked, root1Node35Step1Chunk4_3_checked, root1Node35Step1Chunk4_4_checked, root1Node35Step1Chunk4_5_checked, root1Node35Step1Chunk5_0_checked, root1Node35Step1Chunk5_1_checked, root1Node35Step1Chunk5_2_checked, root1Node35Step1Chunk5_3_checked, root1Node35Step1Chunk5_4_checked, root1Node35Step1Chunk5_5_checked, root1Node35Step1Chunk6_0_checked, root1Node35Step1Chunk6_1_checked, root1Node35Step1Chunk6_2_checked, root1Node35Step1Chunk6_3_checked, root1Node35Step1Chunk6_4_checked, root1Node35Step1Chunk6_5_checked, root1Node35Step1Chunk7_0_checked, root1Node35Step1Chunk7_1_checked, root1Node35Step1Chunk7_2_checked, root1Node35Step1Chunk7_3_checked, root1Node35Step1Chunk7_4_checked, root1Node35Step1Chunk7_5_checked, root1Node35Step1Chunk8_0_checked, root1Node35Step1Chunk8_1_checked, root1Node35Step1Chunk8_2_checked, root1Node35Step1Chunk8_3_checked, root1Node35Step1Chunk8_4_checked, root1Node35Step1Chunk8_5_checked, Bool.true_and])
theorem root1Node35Step1_checked :
    checkReplacement table34 root1Node35Domains0 root1Node35Domains1 = true := by
  exact checkReplacement_of_fast_rest _ root1Node35Domains0 root1Node35Domains1
    root1Node35Domains0Fast root1Node35Domains1Fast
    root1Node35Domains0_fast_eq root1Node35Domains1_fast_eq
    root1Node35Step1Narrowing_checked (by decide)
def root1Node35Domains2 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0),(8,0)]
  | 2 => [(4,5),(7,3)]
  | 3 => [(4,2),(7,0)]
  | 4 => [(5,3),(8,3)]
  | 5 => [(7,5),(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(0,0),(6,4)]
  | 9 => [(1,2),(7,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(2,2),(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(1,5),(7,5)]
  | 16 => [(0,3),(6,1)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(0,1),(4,1),(5,1),(8,1)]
  | 21 => [(4,4),(7,2)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(2,0),(2,2)]
  | 25 => [(3,3),(7,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3),(8,3)]
  | 29 => [(1,0),(5,2),(5,5)]
  | 30 => [(1,1),(7,1)]
  | 31 => [(4,1),(7,5)]
  | 32 => [(0,2),(6,0)]
  | 33 => [(1,1),(3,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(1,4),(6,4)]
  | 38 => [(0,5),(1,2)]
  | 39 => [(4,0),(4,4),(8,4)]
  | 40 => [(4,0),(5,0),(8,0)]
  | 41 => [(7,3)]
  | 42 => [(5,2),(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3),(6,0)]
  | 49 => [(5,1),(7,1),(8,1)]
  | 50 => [(0,1),(1,5),(7,5)]
  | 51 => [(0,0),(0,1),(6,4)]
  | 52 => [(1,2),(6,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2),(8,2)]
  | 59 => [(5,0),(5,3),(8,0)]
  | 60 => [(4,5),(7,3),(8,5)]
  | 61 => [(0,3),(1,0)]
  | 62 => [(7,1),(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(7,4),(8,4)]
  | 69 => [(0,0),(6,3),(6,4)]
  | 70 => [(5,0),(5,3)]
  | 71 => [(4,5),(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5),(8,5)]
  | 75 => [(1,0)]
  | 76 => [(2,1),(7,1)]
  | 77 => [(0,2),(1,5),(7,5)]
  | 78 => [(0,0),(0,5),(6,3)]
  | 79 => [(4,4),(7,2)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3)]
  | 82 => [(4,4),(7,2),(8,2)]
  | 83 => [(0,0),(4,0),(5,0),(8,0)]
  | 84 => [(3,2),(4,5),(7,3)]
  | 85 => [(1,1),(6,1),(7,1)]
  | 86 => [(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,5)]
  | 88 => [(0,4),(1,1),(7,1)]
  | 89 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root1Node35Domains2Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0),(8,0)]
  | 2 => some [(4,5),(7,3)]
  | 3 => some [(4,2),(7,0)]
  | 4 => some [(5,3),(8,3)]
  | 5 => some [(7,5),(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(0,0),(6,4)]
  | 9 => some [(1,2),(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(2,2),(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(1,5),(7,5)]
  | 16 => some [(0,3),(6,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(0,1),(4,1),(5,1),(8,1)]
  | 21 => some [(4,4),(7,2)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(2,0),(2,2)]
  | 25 => some [(3,3),(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3),(8,3)]
  | 29 => some [(1,0),(5,2),(5,5)]
  | 30 => some [(1,1),(7,1)]
  | 31 => some [(4,1),(7,5)]
  | 32 => some [(0,2),(6,0)]
  | 33 => some [(1,1),(3,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4),(6,4)]
  | 38 => some [(0,5),(1,2)]
  | 39 => some [(4,0),(4,4),(8,4)]
  | 40 => some [(4,0),(5,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(5,2),(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3),(6,0)]
  | 49 => some [(5,1),(7,1),(8,1)]
  | 50 => some [(0,1),(1,5),(7,5)]
  | 51 => some [(0,0),(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2),(8,2)]
  | 59 => some [(5,0),(5,3),(8,0)]
  | 60 => some [(4,5),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(6,3),(6,4)]
  | 70 => some [(5,0),(5,3)]
  | 71 => some [(4,5),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(2,1),(7,1)]
  | 77 => some [(0,2),(1,5),(7,5)]
  | 78 => some [(0,0),(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(4,4),(7,2),(8,2)]
  | 83 => some [(0,0),(4,0),(5,0),(8,0)]
  | 84 => some [(3,2),(4,5),(7,3)]
  | 85 => some [(1,1),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(7,1)]
  | 89 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node35Domains2_fast_eq : root1Node35Domains2 = expandDomains root1Node35Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node35Domains2 v = expandDomains root1Node35Domains2Fast v from by decide) v
theorem root1Node35Step2Chunk0_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_0⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk0_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_1⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk0_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_2⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk0_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_3⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk0_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_4⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk0_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows0_5⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk1_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_0⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk1_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_1⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk1_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_2⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk1_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_3⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk1_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_4⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk1_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows1_5⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk2_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_0⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk2_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_1⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk2_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_2⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk2_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_3⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk2_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_4⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk2_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows2_5⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk3_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_0⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk3_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_1⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk3_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_2⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk3_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_3⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk3_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_4⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk3_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows3_5⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk4_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_0⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk4_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_1⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk4_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_2⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk4_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_3⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk4_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_4⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk4_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows4_5⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk5_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_0⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk5_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_1⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk5_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_2⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk5_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_3⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk5_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_4⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk5_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows5_5⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk6_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_0⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk6_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_1⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk6_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_2⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk6_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_3⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk6_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_4⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk6_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows6_5⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk7_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_0⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk7_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_1⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk7_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_2⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk7_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_3⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk7_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_4⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk7_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows7_5⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk8_0_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_0⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk8_1_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_1⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk8_2_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_2⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk8_3_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_3⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk8_4_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_4⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Chunk8_5_checked :
    checkNarrowing ⟨table65Scope, table65Rows8_5⟩
      root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq (by decide)
theorem root1Node35Step2Narrowing_checked :
    checkNarrowing table65 root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkNarrowing_flatten table65Scope [table65Rows0_0,table65Rows0_1,table65Rows0_2,table65Rows0_3,table65Rows0_4,table65Rows0_5,table65Rows1_0,table65Rows1_1,table65Rows1_2,table65Rows1_3,table65Rows1_4,table65Rows1_5,table65Rows2_0,table65Rows2_1,table65Rows2_2,table65Rows2_3,table65Rows2_4,table65Rows2_5,table65Rows3_0,table65Rows3_1,table65Rows3_2,table65Rows3_3,table65Rows3_4,table65Rows3_5,table65Rows4_0,table65Rows4_1,table65Rows4_2,table65Rows4_3,table65Rows4_4,table65Rows4_5,table65Rows5_0,table65Rows5_1,table65Rows5_2,table65Rows5_3,table65Rows5_4,table65Rows5_5,table65Rows6_0,table65Rows6_1,table65Rows6_2,table65Rows6_3,table65Rows6_4,table65Rows6_5,table65Rows7_0,table65Rows7_1,table65Rows7_2,table65Rows7_3,table65Rows7_4,table65Rows7_5,table65Rows8_0,table65Rows8_1,table65Rows8_2,table65Rows8_3,table65Rows8_4,table65Rows8_5]
    root1Node35Domains1 root1Node35Domains2 (by
      simp only [List.all_cons, List.all_nil, root1Node35Step2Chunk0_0_checked, root1Node35Step2Chunk0_1_checked, root1Node35Step2Chunk0_2_checked, root1Node35Step2Chunk0_3_checked, root1Node35Step2Chunk0_4_checked, root1Node35Step2Chunk0_5_checked, root1Node35Step2Chunk1_0_checked, root1Node35Step2Chunk1_1_checked, root1Node35Step2Chunk1_2_checked, root1Node35Step2Chunk1_3_checked, root1Node35Step2Chunk1_4_checked, root1Node35Step2Chunk1_5_checked, root1Node35Step2Chunk2_0_checked, root1Node35Step2Chunk2_1_checked, root1Node35Step2Chunk2_2_checked, root1Node35Step2Chunk2_3_checked, root1Node35Step2Chunk2_4_checked, root1Node35Step2Chunk2_5_checked, root1Node35Step2Chunk3_0_checked, root1Node35Step2Chunk3_1_checked, root1Node35Step2Chunk3_2_checked, root1Node35Step2Chunk3_3_checked, root1Node35Step2Chunk3_4_checked, root1Node35Step2Chunk3_5_checked, root1Node35Step2Chunk4_0_checked, root1Node35Step2Chunk4_1_checked, root1Node35Step2Chunk4_2_checked, root1Node35Step2Chunk4_3_checked, root1Node35Step2Chunk4_4_checked, root1Node35Step2Chunk4_5_checked, root1Node35Step2Chunk5_0_checked, root1Node35Step2Chunk5_1_checked, root1Node35Step2Chunk5_2_checked, root1Node35Step2Chunk5_3_checked, root1Node35Step2Chunk5_4_checked, root1Node35Step2Chunk5_5_checked, root1Node35Step2Chunk6_0_checked, root1Node35Step2Chunk6_1_checked, root1Node35Step2Chunk6_2_checked, root1Node35Step2Chunk6_3_checked, root1Node35Step2Chunk6_4_checked, root1Node35Step2Chunk6_5_checked, root1Node35Step2Chunk7_0_checked, root1Node35Step2Chunk7_1_checked, root1Node35Step2Chunk7_2_checked, root1Node35Step2Chunk7_3_checked, root1Node35Step2Chunk7_4_checked, root1Node35Step2Chunk7_5_checked, root1Node35Step2Chunk8_0_checked, root1Node35Step2Chunk8_1_checked, root1Node35Step2Chunk8_2_checked, root1Node35Step2Chunk8_3_checked, root1Node35Step2Chunk8_4_checked, root1Node35Step2Chunk8_5_checked, Bool.true_and])
theorem root1Node35Step2_checked :
    checkReplacement table65 root1Node35Domains1 root1Node35Domains2 = true := by
  exact checkReplacement_of_fast_rest _ root1Node35Domains1 root1Node35Domains2
    root1Node35Domains1Fast root1Node35Domains2Fast
    root1Node35Domains1_fast_eq root1Node35Domains2_fast_eq
    root1Node35Step2Narrowing_checked (by decide)
def root1Node35Domains3 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0),(8,0)]
  | 2 => [(4,5),(7,3)]
  | 3 => [(4,2),(7,0)]
  | 4 => [(5,3),(8,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(0,0),(6,4)]
  | 9 => [(1,2),(7,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(1,5),(7,5)]
  | 16 => [(0,3),(6,1)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1),(5,1),(8,1)]
  | 21 => [(4,4),(7,2)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(2,0),(2,2)]
  | 25 => [(3,3),(7,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3),(8,3)]
  | 29 => [(5,2),(5,5)]
  | 30 => [(1,1),(7,1)]
  | 31 => [(4,1),(7,5)]
  | 32 => [(0,2),(6,0)]
  | 33 => [(1,1),(3,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(1,4),(6,4)]
  | 38 => [(0,5),(1,2)]
  | 39 => [(4,4),(8,4)]
  | 40 => [(4,0),(5,0),(8,0)]
  | 41 => [(7,3)]
  | 42 => [(5,2),(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3),(6,0)]
  | 49 => [(7,1),(8,1)]
  | 50 => [(1,5),(7,5)]
  | 51 => [(0,0),(0,1),(6,4)]
  | 52 => [(1,2),(6,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2),(8,2)]
  | 59 => [(5,0),(5,3),(8,0)]
  | 60 => [(4,5),(7,3),(8,5)]
  | 61 => [(0,3),(1,0)]
  | 62 => [(7,1),(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(7,4),(8,4)]
  | 69 => [(0,0),(6,3),(6,4)]
  | 70 => [(5,0),(5,3)]
  | 71 => [(4,5),(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5),(8,5)]
  | 75 => [(1,0)]
  | 76 => [(2,1),(7,1)]
  | 77 => [(0,2),(1,5),(7,5)]
  | 78 => [(0,0),(0,5),(6,3)]
  | 79 => [(4,4),(7,2)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3)]
  | 82 => [(4,4),(7,2),(8,2)]
  | 83 => [(0,0),(4,0),(5,0),(8,0)]
  | 84 => [(3,2),(4,5),(7,3)]
  | 85 => [(1,1),(6,1),(7,1)]
  | 86 => [(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,5)]
  | 88 => [(0,4),(1,1),(7,1)]
  | 89 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root1Node35Domains3Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0),(8,0)]
  | 2 => some [(4,5),(7,3)]
  | 3 => some [(4,2),(7,0)]
  | 4 => some [(5,3),(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(0,0),(6,4)]
  | 9 => some [(1,2),(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(1,5),(7,5)]
  | 16 => some [(0,3),(6,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1),(5,1),(8,1)]
  | 21 => some [(4,4),(7,2)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(2,0),(2,2)]
  | 25 => some [(3,3),(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3),(8,3)]
  | 29 => some [(5,2),(5,5)]
  | 30 => some [(1,1),(7,1)]
  | 31 => some [(4,1),(7,5)]
  | 32 => some [(0,2),(6,0)]
  | 33 => some [(1,1),(3,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4),(6,4)]
  | 38 => some [(0,5),(1,2)]
  | 39 => some [(4,4),(8,4)]
  | 40 => some [(4,0),(5,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(5,2),(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3),(6,0)]
  | 49 => some [(7,1),(8,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(0,0),(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2),(8,2)]
  | 59 => some [(5,0),(5,3),(8,0)]
  | 60 => some [(4,5),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(6,3),(6,4)]
  | 70 => some [(5,0),(5,3)]
  | 71 => some [(4,5),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(2,1),(7,1)]
  | 77 => some [(0,2),(1,5),(7,5)]
  | 78 => some [(0,0),(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(4,4),(7,2),(8,2)]
  | 83 => some [(0,0),(4,0),(5,0),(8,0)]
  | 84 => some [(3,2),(4,5),(7,3)]
  | 85 => some [(1,1),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(7,1)]
  | 89 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node35Domains3_fast_eq : root1Node35Domains3 = expandDomains root1Node35Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node35Domains3 v = expandDomains root1Node35Domains3Fast v from by decide) v
theorem root1Node35Step3Chunk0_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_0⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk0_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_1⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk0_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_2⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk0_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_3⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk0_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_4⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk0_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows0_5⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk1_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_0⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk1_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_1⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk1_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_2⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk1_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_3⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk1_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_4⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk1_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows1_5⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk2_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_0⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk2_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_1⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk2_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_2⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk2_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_3⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk2_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_4⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk2_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows2_5⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk3_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_0⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk3_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_1⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk3_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_2⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk3_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_3⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk3_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_4⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk3_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows3_5⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk4_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_0⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk4_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_1⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk4_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_2⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk4_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_3⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk4_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_4⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk4_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows4_5⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk5_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_0⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk5_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_1⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk5_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_2⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk5_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_3⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk5_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_4⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk5_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows5_5⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk6_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_0⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk6_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_1⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk6_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_2⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk6_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_3⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk6_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_4⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk6_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows6_5⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk7_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_0⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk7_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_1⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk7_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_2⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk7_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_3⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk7_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_4⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk7_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows7_5⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk8_0_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_0⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk8_1_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_1⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk8_2_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_2⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk8_3_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_3⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk8_4_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_4⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Chunk8_5_checked :
    checkNarrowing ⟨table12Scope, table12Rows8_5⟩
      root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq (by decide)
theorem root1Node35Step3Narrowing_checked :
    checkNarrowing table12 root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkNarrowing_flatten table12Scope [table12Rows0_0,table12Rows0_1,table12Rows0_2,table12Rows0_3,table12Rows0_4,table12Rows0_5,table12Rows1_0,table12Rows1_1,table12Rows1_2,table12Rows1_3,table12Rows1_4,table12Rows1_5,table12Rows2_0,table12Rows2_1,table12Rows2_2,table12Rows2_3,table12Rows2_4,table12Rows2_5,table12Rows3_0,table12Rows3_1,table12Rows3_2,table12Rows3_3,table12Rows3_4,table12Rows3_5,table12Rows4_0,table12Rows4_1,table12Rows4_2,table12Rows4_3,table12Rows4_4,table12Rows4_5,table12Rows5_0,table12Rows5_1,table12Rows5_2,table12Rows5_3,table12Rows5_4,table12Rows5_5,table12Rows6_0,table12Rows6_1,table12Rows6_2,table12Rows6_3,table12Rows6_4,table12Rows6_5,table12Rows7_0,table12Rows7_1,table12Rows7_2,table12Rows7_3,table12Rows7_4,table12Rows7_5,table12Rows8_0,table12Rows8_1,table12Rows8_2,table12Rows8_3,table12Rows8_4,table12Rows8_5]
    root1Node35Domains2 root1Node35Domains3 (by
      simp only [List.all_cons, List.all_nil, root1Node35Step3Chunk0_0_checked, root1Node35Step3Chunk0_1_checked, root1Node35Step3Chunk0_2_checked, root1Node35Step3Chunk0_3_checked, root1Node35Step3Chunk0_4_checked, root1Node35Step3Chunk0_5_checked, root1Node35Step3Chunk1_0_checked, root1Node35Step3Chunk1_1_checked, root1Node35Step3Chunk1_2_checked, root1Node35Step3Chunk1_3_checked, root1Node35Step3Chunk1_4_checked, root1Node35Step3Chunk1_5_checked, root1Node35Step3Chunk2_0_checked, root1Node35Step3Chunk2_1_checked, root1Node35Step3Chunk2_2_checked, root1Node35Step3Chunk2_3_checked, root1Node35Step3Chunk2_4_checked, root1Node35Step3Chunk2_5_checked, root1Node35Step3Chunk3_0_checked, root1Node35Step3Chunk3_1_checked, root1Node35Step3Chunk3_2_checked, root1Node35Step3Chunk3_3_checked, root1Node35Step3Chunk3_4_checked, root1Node35Step3Chunk3_5_checked, root1Node35Step3Chunk4_0_checked, root1Node35Step3Chunk4_1_checked, root1Node35Step3Chunk4_2_checked, root1Node35Step3Chunk4_3_checked, root1Node35Step3Chunk4_4_checked, root1Node35Step3Chunk4_5_checked, root1Node35Step3Chunk5_0_checked, root1Node35Step3Chunk5_1_checked, root1Node35Step3Chunk5_2_checked, root1Node35Step3Chunk5_3_checked, root1Node35Step3Chunk5_4_checked, root1Node35Step3Chunk5_5_checked, root1Node35Step3Chunk6_0_checked, root1Node35Step3Chunk6_1_checked, root1Node35Step3Chunk6_2_checked, root1Node35Step3Chunk6_3_checked, root1Node35Step3Chunk6_4_checked, root1Node35Step3Chunk6_5_checked, root1Node35Step3Chunk7_0_checked, root1Node35Step3Chunk7_1_checked, root1Node35Step3Chunk7_2_checked, root1Node35Step3Chunk7_3_checked, root1Node35Step3Chunk7_4_checked, root1Node35Step3Chunk7_5_checked, root1Node35Step3Chunk8_0_checked, root1Node35Step3Chunk8_1_checked, root1Node35Step3Chunk8_2_checked, root1Node35Step3Chunk8_3_checked, root1Node35Step3Chunk8_4_checked, root1Node35Step3Chunk8_5_checked, Bool.true_and])
theorem root1Node35Step3_checked :
    checkReplacement table12 root1Node35Domains2 root1Node35Domains3 = true := by
  exact checkReplacement_of_fast_rest _ root1Node35Domains2 root1Node35Domains3
    root1Node35Domains2Fast root1Node35Domains3Fast
    root1Node35Domains2_fast_eq root1Node35Domains3_fast_eq
    root1Node35Step3Narrowing_checked (by decide)
def root1Node35Domains4 (v : Fin 91) : List State :=
  match v.val with
  | 0 => [(8,2)]
  | 1 => [(5,0),(8,0)]
  | 2 => [(4,5),(7,3)]
  | 3 => [(4,2),(7,0)]
  | 4 => [(5,3),(8,3)]
  | 5 => [(8,5)]
  | 6 => [(0,4)]
  | 7 => [(5,4)]
  | 8 => [(0,0),(6,4)]
  | 9 => [(1,2),(7,2)]
  | 10 => [(7,4)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(1,5),(7,5)]
  | 16 => [(0,3),(6,1)]
  | 17 => [(4,1)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1),(5,1),(8,1)]
  | 21 => [(4,4),(7,2)]
  | 22 => [(1,4),(7,4)]
  | 23 => [(0,5),(6,3)]
  | 24 => [(2,0),(2,2)]
  | 25 => [(3,3),(7,3)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3),(8,3)]
  | 29 => [(5,2),(5,5)]
  | 30 => [(1,1),(7,1)]
  | 31 => [(4,1),(7,5)]
  | 32 => [(0,2),(6,0)]
  | 33 => [(1,1),(3,1)]
  | 34 => [(0,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(1,4),(6,4)]
  | 38 => [(0,5),(1,2)]
  | 39 => [(4,4),(8,4)]
  | 40 => [(4,0),(8,0)]
  | 41 => [(7,3)]
  | 42 => [(5,2),(8,2)]
  | 43 => [(5,0)]
  | 44 => [(4,5)]
  | 45 => [(1,0)]
  | 46 => [(7,1)]
  | 47 => [(7,5)]
  | 48 => [(0,3),(6,0)]
  | 49 => [(7,1),(8,1)]
  | 50 => [(1,5),(7,5)]
  | 51 => [(0,1),(6,4)]
  | 52 => [(1,2),(6,2)]
  | 53 => [(8,4)]
  | 54 => [(0,0)]
  | 55 => [(7,2)]
  | 56 => [(4,0)]
  | 57 => [(7,3)]
  | 58 => [(4,2),(8,2)]
  | 59 => [(5,0),(5,3),(8,0)]
  | 60 => [(4,5),(7,3),(8,5)]
  | 61 => [(0,3),(1,0)]
  | 62 => [(7,1),(8,1)]
  | 63 => [(1,5)]
  | 64 => [(6,1)]
  | 65 => [(5,1)]
  | 66 => [(0,1)]
  | 67 => [(6,2)]
  | 68 => [(7,4),(8,4)]
  | 69 => [(0,0),(6,3),(6,4)]
  | 70 => [(5,0),(5,3)]
  | 71 => [(4,5),(5,5),(8,5)]
  | 72 => [(7,0)]
  | 73 => [(8,3)]
  | 74 => [(5,5),(8,5)]
  | 75 => [(1,0)]
  | 76 => [(2,1),(7,1)]
  | 77 => [(0,2),(1,5),(7,5)]
  | 78 => [(0,0),(0,5),(6,3)]
  | 79 => [(4,4),(7,2)]
  | 80 => [(1,4),(7,4)]
  | 81 => [(0,5),(1,3),(6,3)]
  | 82 => [(4,4),(7,2),(8,2)]
  | 83 => [(0,0),(4,0),(5,0),(8,0)]
  | 84 => [(3,2),(4,5),(7,3)]
  | 85 => [(1,1),(6,1),(7,1)]
  | 86 => [(4,1),(7,5),(8,1)]
  | 87 => [(0,2),(6,0),(6,5)]
  | 88 => [(0,4),(1,1),(7,1)]
  | 89 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root1Node35Domains4Fast (v : Fin 91) : Option (List State) :=
  match v.val with
  | 0 => some [(8,2)]
  | 1 => some [(5,0),(8,0)]
  | 2 => some [(4,5),(7,3)]
  | 3 => some [(4,2),(7,0)]
  | 4 => some [(5,3),(8,3)]
  | 5 => some [(8,5)]
  | 6 => some [(0,4)]
  | 7 => some [(5,4)]
  | 8 => some [(0,0),(6,4)]
  | 9 => some [(1,2),(7,2)]
  | 10 => some [(7,4)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(1,5),(7,5)]
  | 16 => some [(0,3),(6,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1),(5,1),(8,1)]
  | 21 => some [(4,4),(7,2)]
  | 22 => some [(1,4),(7,4)]
  | 23 => some [(0,5),(6,3)]
  | 24 => some [(2,0),(2,2)]
  | 25 => some [(3,3),(7,3)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3),(8,3)]
  | 29 => some [(5,2),(5,5)]
  | 30 => some [(1,1),(7,1)]
  | 31 => some [(4,1),(7,5)]
  | 32 => some [(0,2),(6,0)]
  | 33 => some [(1,1),(3,1)]
  | 34 => some [(0,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(1,4),(6,4)]
  | 38 => some [(0,5),(1,2)]
  | 39 => some [(4,4),(8,4)]
  | 40 => some [(4,0),(8,0)]
  | 41 => some [(7,3)]
  | 42 => some [(5,2),(8,2)]
  | 43 => some [(5,0)]
  | 44 => some [(4,5)]
  | 45 => some [(1,0)]
  | 46 => some [(7,1)]
  | 47 => some [(7,5)]
  | 48 => some [(0,3),(6,0)]
  | 49 => some [(7,1),(8,1)]
  | 50 => some [(1,5),(7,5)]
  | 51 => some [(0,1),(6,4)]
  | 52 => some [(1,2),(6,2)]
  | 53 => some [(8,4)]
  | 54 => some [(0,0)]
  | 55 => some [(7,2)]
  | 56 => some [(4,0)]
  | 57 => some [(7,3)]
  | 58 => some [(4,2),(8,2)]
  | 59 => some [(5,0),(5,3),(8,0)]
  | 60 => some [(4,5),(7,3),(8,5)]
  | 61 => some [(0,3),(1,0)]
  | 62 => some [(7,1),(8,1)]
  | 63 => some [(1,5)]
  | 64 => some [(6,1)]
  | 65 => some [(5,1)]
  | 66 => some [(0,1)]
  | 67 => some [(6,2)]
  | 68 => some [(7,4),(8,4)]
  | 69 => some [(0,0),(6,3),(6,4)]
  | 70 => some [(5,0),(5,3)]
  | 71 => some [(4,5),(5,5),(8,5)]
  | 72 => some [(7,0)]
  | 73 => some [(8,3)]
  | 74 => some [(5,5),(8,5)]
  | 75 => some [(1,0)]
  | 76 => some [(2,1),(7,1)]
  | 77 => some [(0,2),(1,5),(7,5)]
  | 78 => some [(0,0),(0,5),(6,3)]
  | 79 => some [(4,4),(7,2)]
  | 80 => some [(1,4),(7,4)]
  | 81 => some [(0,5),(1,3),(6,3)]
  | 82 => some [(4,4),(7,2),(8,2)]
  | 83 => some [(0,0),(4,0),(5,0),(8,0)]
  | 84 => some [(3,2),(4,5),(7,3)]
  | 85 => some [(1,1),(6,1),(7,1)]
  | 86 => some [(4,1),(7,5),(8,1)]
  | 87 => some [(0,2),(6,0),(6,5)]
  | 88 => some [(0,4),(1,1),(7,1)]
  | 89 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root1Node35Domains4_fast_eq : root1Node35Domains4 = expandDomains root1Node35Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 91, root1Node35Domains4 v = expandDomains root1Node35Domains4Fast v from by decide) v
theorem root1Node35Step4Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_of_fast _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq (by decide)
theorem root1Node35Step4Narrowing_checked :
    checkNarrowing table13 root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkNarrowing_flatten table13Scope [table13Rows0_0,table13Rows0_1,table13Rows0_2,table13Rows0_3,table13Rows0_4,table13Rows0_5,table13Rows1_0,table13Rows1_1,table13Rows1_2,table13Rows1_3,table13Rows1_4,table13Rows1_5,table13Rows2_0,table13Rows2_1,table13Rows2_2,table13Rows2_3,table13Rows2_4,table13Rows2_5,table13Rows3_0,table13Rows3_1,table13Rows3_2,table13Rows3_3,table13Rows3_4,table13Rows3_5,table13Rows4_0,table13Rows4_1,table13Rows4_2,table13Rows4_3,table13Rows4_4,table13Rows4_5,table13Rows5_0,table13Rows5_1,table13Rows5_2,table13Rows5_3,table13Rows5_4,table13Rows5_5,table13Rows6_0,table13Rows6_1,table13Rows6_2,table13Rows6_3,table13Rows6_4,table13Rows6_5,table13Rows7_0,table13Rows7_1,table13Rows7_2,table13Rows7_3,table13Rows7_4,table13Rows7_5,table13Rows8_0,table13Rows8_1,table13Rows8_2,table13Rows8_3,table13Rows8_4,table13Rows8_5]
    root1Node35Domains3 root1Node35Domains4 (by
      simp only [List.all_cons, List.all_nil, root1Node35Step4Chunk0_0_checked, root1Node35Step4Chunk0_1_checked, root1Node35Step4Chunk0_2_checked, root1Node35Step4Chunk0_3_checked, root1Node35Step4Chunk0_4_checked, root1Node35Step4Chunk0_5_checked, root1Node35Step4Chunk1_0_checked, root1Node35Step4Chunk1_1_checked, root1Node35Step4Chunk1_2_checked, root1Node35Step4Chunk1_3_checked, root1Node35Step4Chunk1_4_checked, root1Node35Step4Chunk1_5_checked, root1Node35Step4Chunk2_0_checked, root1Node35Step4Chunk2_1_checked, root1Node35Step4Chunk2_2_checked, root1Node35Step4Chunk2_3_checked, root1Node35Step4Chunk2_4_checked, root1Node35Step4Chunk2_5_checked, root1Node35Step4Chunk3_0_checked, root1Node35Step4Chunk3_1_checked, root1Node35Step4Chunk3_2_checked, root1Node35Step4Chunk3_3_checked, root1Node35Step4Chunk3_4_checked, root1Node35Step4Chunk3_5_checked, root1Node35Step4Chunk4_0_checked, root1Node35Step4Chunk4_1_checked, root1Node35Step4Chunk4_2_checked, root1Node35Step4Chunk4_3_checked, root1Node35Step4Chunk4_4_checked, root1Node35Step4Chunk4_5_checked, root1Node35Step4Chunk5_0_checked, root1Node35Step4Chunk5_1_checked, root1Node35Step4Chunk5_2_checked, root1Node35Step4Chunk5_3_checked, root1Node35Step4Chunk5_4_checked, root1Node35Step4Chunk5_5_checked, root1Node35Step4Chunk6_0_checked, root1Node35Step4Chunk6_1_checked, root1Node35Step4Chunk6_2_checked, root1Node35Step4Chunk6_3_checked, root1Node35Step4Chunk6_4_checked, root1Node35Step4Chunk6_5_checked, root1Node35Step4Chunk7_0_checked, root1Node35Step4Chunk7_1_checked, root1Node35Step4Chunk7_2_checked, root1Node35Step4Chunk7_3_checked, root1Node35Step4Chunk7_4_checked, root1Node35Step4Chunk7_5_checked, root1Node35Step4Chunk8_0_checked, root1Node35Step4Chunk8_1_checked, root1Node35Step4Chunk8_2_checked, root1Node35Step4Chunk8_3_checked, root1Node35Step4Chunk8_4_checked, root1Node35Step4Chunk8_5_checked, Bool.true_and])
theorem root1Node35Step4_checked :
    checkReplacement table13 root1Node35Domains3 root1Node35Domains4 = true := by
  exact checkReplacement_of_fast_rest _ root1Node35Domains3 root1Node35Domains4
    root1Node35Domains3Fast root1Node35Domains4Fast
    root1Node35Domains3_fast_eq root1Node35Domains4_fast_eq
    root1Node35Step4Narrowing_checked (by decide)
end SpectreFinite.HexSearch.RadiusFive
