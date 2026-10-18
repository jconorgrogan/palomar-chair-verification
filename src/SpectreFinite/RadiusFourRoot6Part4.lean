module

public import SpectreFinite.RadiusFourRoot6Part3
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable0
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable22
public import SpectreFinite.RadiusFourTable46
public import SpectreFinite.RadiusFourTable5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node11Domains0 : Domains 61 State := restrict root6Node10Domains3 0 (7,4)
def root6Node11Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(0,0),(1,3),(6,3)]
  | 2 => some [(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,1),(8,1)]
  | 6 => some [(0,2),(1,5),(6,5)]
  | 7 => some [(0,4),(1,1),(6,1)]
  | 8 => some [(5,1),(5,4),(8,1)]
  | 9 => some [(0,0),(0,1),(6,4),(6,5)]
  | 10 => some [(0,4),(1,2),(6,2),(7,2)]
  | 11 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => some [(5,2),(5,5)]
  | 13 => some [(7,0),(8,0)]
  | 14 => some [(4,3),(8,3)]
  | 15 => some [(1,5),(3,5),(5,5)]
  | 16 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 18 => some [(0,1),(1,4),(6,5)]
  | 19 => some [(0,4),(0,5),(6,2)]
  | 20 => some [(4,4),(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,0),(2,4),(4,4)]
  | 24 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 25 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 26 => some [(2,5),(4,5),(7,5),(8,5)]
  | 27 => some [(1,0),(6,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(3,1),(7,1)]
  | 32 => some [(0,1),(1,5),(6,5),(7,5)]
  | 33 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(1,0),(4,2),(7,0),(8,2)]
  | 42 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1),(8,4)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(4,0),(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(5,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node11Domains0_fast_eq : root6Node11Domains0 = expandDomains root6Node11Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node11Domains0 v = expandDomains root6Node11Domains0Fast v from by decide) v
def root6Node11Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3),(6,3)]
  | 2 => [(7,2),(8,2)]
  | 3 => [(4,0),(5,0),(7,4),(8,0)]
  | 4 => [(1,3),(4,5),(7,3)]
  | 5 => [(4,1),(8,1)]
  | 6 => [(0,2),(6,5)]
  | 7 => [(0,4),(1,1)]
  | 8 => [(5,1),(5,4),(8,1)]
  | 9 => [(0,0),(0,1),(6,4),(6,5)]
  | 10 => [(0,4),(1,2),(6,2),(7,2)]
  | 11 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => [(5,2),(5,5)]
  | 13 => [(7,0),(8,0)]
  | 14 => [(4,3),(8,3)]
  | 15 => [(1,5),(3,5),(5,5)]
  | 16 => [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 17 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 18 => [(0,1),(1,4),(6,5)]
  | 19 => [(0,4),(0,5),(6,2)]
  | 20 => [(4,4),(5,4),(8,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(2,0),(2,4),(4,4)]
  | 24 => [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 25 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 26 => [(2,5),(4,5),(7,5),(8,5)]
  | 27 => [(1,0),(6,0),(7,0)]
  | 28 => [(4,3),(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(3,1),(7,1)]
  | 32 => [(0,1),(1,5),(6,5),(7,5)]
  | 33 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 34 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(7,4),(8,0)]
  | 37 => [(1,3),(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(1,0),(4,2),(7,0),(8,2)]
  | 42 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => [(5,1),(5,4),(8,1),(8,4)]
  | 44 => [(0,1),(6,4),(6,5)]
  | 45 => [(0,4),(1,2),(6,2)]
  | 46 => [(5,4),(8,4)]
  | 47 => [(0,0),(6,4)]
  | 48 => [(1,2),(7,2)]
  | 49 => [(4,0),(7,4),(8,4)]
  | 50 => [(5,5),(7,5),(8,5)]
  | 51 => [(0,3),(1,0),(7,0)]
  | 52 => [(4,3),(7,1),(8,1)]
  | 53 => [(1,5),(3,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(4,1),(5,1),(8,1)]
  | 56 => [(4,2),(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => [(1,3),(3,3),(5,3),(7,3),(8,3)]
def root6Node11Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3),(6,3)]
  | 2 => some [(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,1),(8,1)]
  | 6 => some [(0,2),(6,5)]
  | 7 => some [(0,4),(1,1)]
  | 8 => some [(5,1),(5,4),(8,1)]
  | 9 => some [(0,0),(0,1),(6,4),(6,5)]
  | 10 => some [(0,4),(1,2),(6,2),(7,2)]
  | 11 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => some [(5,2),(5,5)]
  | 13 => some [(7,0),(8,0)]
  | 14 => some [(4,3),(8,3)]
  | 15 => some [(1,5),(3,5),(5,5)]
  | 16 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 18 => some [(0,1),(1,4),(6,5)]
  | 19 => some [(0,4),(0,5),(6,2)]
  | 20 => some [(4,4),(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,0),(2,4),(4,4)]
  | 24 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 25 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 26 => some [(2,5),(4,5),(7,5),(8,5)]
  | 27 => some [(1,0),(6,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(3,1),(7,1)]
  | 32 => some [(0,1),(1,5),(6,5),(7,5)]
  | 33 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(1,0),(4,2),(7,0),(8,2)]
  | 42 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1),(8,4)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(4,0),(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(5,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node11Domains1_fast_eq : root6Node11Domains1 = expandDomains root6Node11Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node11Domains1 v = expandDomains root6Node11Domains1Fast v from by decide) v
theorem root6Node11Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root6Node11Domains0 root6Node11Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node11Domains0 root6Node11Domains1
    root6Node11Domains0Fast root6Node11Domains1Fast
    root6Node11Domains0_fast_eq root6Node11Domains1_fast_eq (by decide)
theorem root6Node11Step1_checked :
    checkReplacement table0 root6Node11Domains0 root6Node11Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node11Step1Chunk0_0_checked, root6Node11Step1Chunk0_1_checked, root6Node11Step1Chunk0_2_checked, root6Node11Step1Chunk0_3_checked, root6Node11Step1Chunk0_4_checked, root6Node11Step1Chunk0_5_checked, root6Node11Step1Chunk1_0_checked, root6Node11Step1Chunk1_1_checked, root6Node11Step1Chunk1_2_checked, root6Node11Step1Chunk1_3_checked, root6Node11Step1Chunk1_4_checked, root6Node11Step1Chunk1_5_checked, root6Node11Step1Chunk2_0_checked, root6Node11Step1Chunk2_1_checked, root6Node11Step1Chunk2_2_checked, root6Node11Step1Chunk2_3_checked, root6Node11Step1Chunk2_4_checked, root6Node11Step1Chunk2_5_checked, root6Node11Step1Chunk3_0_checked, root6Node11Step1Chunk3_1_checked, root6Node11Step1Chunk3_2_checked, root6Node11Step1Chunk3_3_checked, root6Node11Step1Chunk3_4_checked, root6Node11Step1Chunk3_5_checked, root6Node11Step1Chunk4_0_checked, root6Node11Step1Chunk4_1_checked, root6Node11Step1Chunk4_2_checked, root6Node11Step1Chunk4_3_checked, root6Node11Step1Chunk4_4_checked, root6Node11Step1Chunk4_5_checked, root6Node11Step1Chunk5_0_checked, root6Node11Step1Chunk5_1_checked, root6Node11Step1Chunk5_2_checked, root6Node11Step1Chunk5_3_checked, root6Node11Step1Chunk5_4_checked, root6Node11Step1Chunk5_5_checked, root6Node11Step1Chunk6_0_checked, root6Node11Step1Chunk6_1_checked, root6Node11Step1Chunk6_2_checked, root6Node11Step1Chunk6_3_checked, root6Node11Step1Chunk6_4_checked, root6Node11Step1Chunk6_5_checked, root6Node11Step1Chunk7_0_checked, root6Node11Step1Chunk7_1_checked, root6Node11Step1Chunk7_2_checked, root6Node11Step1Chunk7_3_checked, root6Node11Step1Chunk7_4_checked, root6Node11Step1Chunk7_5_checked, root6Node11Step1Chunk8_0_checked, root6Node11Step1Chunk8_1_checked, root6Node11Step1Chunk8_2_checked, root6Node11Step1Chunk8_3_checked, root6Node11Step1Chunk8_4_checked, root6Node11Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node12Domains0 : Domains 61 State := restrict root6Node11Domains1 1 (1,3)
def root6Node12Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(7,2),(8,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(4,1),(8,1)]
  | 6 => some [(0,2),(6,5)]
  | 7 => some [(0,4),(1,1)]
  | 8 => some [(5,1),(5,4),(8,1)]
  | 9 => some [(0,0),(0,1),(6,4),(6,5)]
  | 10 => some [(0,4),(1,2),(6,2),(7,2)]
  | 11 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => some [(5,2),(5,5)]
  | 13 => some [(7,0),(8,0)]
  | 14 => some [(4,3),(8,3)]
  | 15 => some [(1,5),(3,5),(5,5)]
  | 16 => some [(0,3),(1,0),(3,0),(6,1),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 18 => some [(0,1),(1,4),(6,5)]
  | 19 => some [(0,4),(0,5),(6,2)]
  | 20 => some [(4,4),(5,4),(8,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,0),(2,4),(4,4)]
  | 24 => some [(0,0),(1,3),(1,4),(6,4),(7,3)]
  | 25 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 26 => some [(2,5),(4,5),(7,5),(8,5)]
  | 27 => some [(1,0),(6,0),(7,0)]
  | 28 => some [(4,3),(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(3,1),(7,1)]
  | 32 => some [(0,1),(1,5),(6,5),(7,5)]
  | 33 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(1,3),(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(1,0),(4,2),(7,0),(8,2)]
  | 42 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1),(8,4)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(0,4),(1,2),(6,2)]
  | 46 => some [(5,4),(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(4,0),(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(5,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node12Domains0_fast_eq : root6Node12Domains0 = expandDomains root6Node12Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node12Domains0 v = expandDomains root6Node12Domains0Fast v from by decide) v
def root6Node12Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(5,0),(8,0)]
  | 4 => [(4,5),(7,3)]
  | 5 => [(4,1),(8,1)]
  | 6 => [(6,5)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
  | 9 => [(0,0),(6,4)]
  | 10 => [(1,2),(7,2)]
  | 11 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => [(5,5)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(1,5),(3,5)]
  | 16 => [(0,3),(6,1)]
  | 17 => [(4,1)]
  | 18 => [(0,1),(1,4),(6,5)]
  | 19 => [(0,5)]
  | 20 => [(4,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(2,0),(2,4)]
  | 24 => [(1,3),(7,3)]
  | 25 => [(5,2)]
  | 26 => [(2,5),(4,5),(7,5),(8,5)]
  | 27 => [(1,0),(6,0),(7,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(3,1),(7,1)]
  | 32 => [(0,1),(6,5)]
  | 33 => [(0,4),(6,2)]
  | 34 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(7,4),(8,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(1,0),(7,0)]
  | 42 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => [(5,1),(5,4),(8,1),(8,4)]
  | 44 => [(0,1),(6,4),(6,5)]
  | 45 => [(1,2),(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(4,0),(7,4),(8,4)]
  | 50 => [(5,5),(7,5),(8,5)]
  | 51 => [(0,3),(1,0),(7,0)]
  | 52 => [(4,3),(7,1),(8,1)]
  | 53 => [(1,5),(3,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(4,1),(5,1),(8,1)]
  | 56 => [(4,2),(4,4),(7,2),(8,2)]
  | 57 => [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => [(1,3),(3,3),(5,3),(7,3),(8,3)]
def root6Node12Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0),(8,0)]
  | 4 => some [(4,5),(7,3)]
  | 5 => some [(4,1),(8,1)]
  | 6 => some [(6,5)]
  | 7 => some [(0,4)]
  | 8 => some [(5,4)]
  | 9 => some [(0,0),(6,4)]
  | 10 => some [(1,2),(7,2)]
  | 11 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(1,5),(3,5)]
  | 16 => some [(0,3),(6,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,1),(1,4),(6,5)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,0),(2,4)]
  | 24 => some [(1,3),(7,3)]
  | 25 => some [(5,2)]
  | 26 => some [(2,5),(4,5),(7,5),(8,5)]
  | 27 => some [(1,0),(6,0),(7,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(3,1),(7,1)]
  | 32 => some [(0,1),(6,5)]
  | 33 => some [(0,4),(6,2)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(7,4),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(1,0),(7,0)]
  | 42 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => some [(5,1),(5,4),(8,1),(8,4)]
  | 44 => some [(0,1),(6,4),(6,5)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(4,0),(7,4),(8,4)]
  | 50 => some [(5,5),(7,5),(8,5)]
  | 51 => some [(0,3),(1,0),(7,0)]
  | 52 => some [(4,3),(7,1),(8,1)]
  | 53 => some [(1,5),(3,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(4,1),(5,1),(8,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(1,4),(4,0),(5,0),(5,3),(7,4),(8,0)]
  | 58 => some [(0,5),(1,3),(4,5),(5,5),(6,3),(7,3),(8,5)]
  | 59 => some [(2,0),(2,2),(2,4),(4,2),(7,0)]
  | _ => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
theorem root6Node12Domains1_fast_eq : root6Node12Domains1 = expandDomains root6Node12Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node12Domains1 v = expandDomains root6Node12Domains1Fast v from by decide) v
theorem root6Node12Step1Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root6Node12Domains0 root6Node12Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains0 root6Node12Domains1
    root6Node12Domains0Fast root6Node12Domains1Fast
    root6Node12Domains0_fast_eq root6Node12Domains1_fast_eq (by decide)
theorem root6Node12Step1_checked :
    checkReplacement table22 root6Node12Domains0 root6Node12Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node12Step1Chunk0_0_checked, root6Node12Step1Chunk0_1_checked, root6Node12Step1Chunk0_2_checked, root6Node12Step1Chunk0_3_checked, root6Node12Step1Chunk0_4_checked, root6Node12Step1Chunk0_5_checked, root6Node12Step1Chunk1_0_checked, root6Node12Step1Chunk1_1_checked, root6Node12Step1Chunk1_2_checked, root6Node12Step1Chunk1_3_checked, root6Node12Step1Chunk1_4_checked, root6Node12Step1Chunk1_5_checked, root6Node12Step1Chunk2_0_checked, root6Node12Step1Chunk2_1_checked, root6Node12Step1Chunk2_2_checked, root6Node12Step1Chunk2_3_checked, root6Node12Step1Chunk2_4_checked, root6Node12Step1Chunk2_5_checked, root6Node12Step1Chunk3_0_checked, root6Node12Step1Chunk3_1_checked, root6Node12Step1Chunk3_2_checked, root6Node12Step1Chunk3_3_checked, root6Node12Step1Chunk3_4_checked, root6Node12Step1Chunk3_5_checked, root6Node12Step1Chunk4_0_checked, root6Node12Step1Chunk4_1_checked, root6Node12Step1Chunk4_2_checked, root6Node12Step1Chunk4_3_checked, root6Node12Step1Chunk4_4_checked, root6Node12Step1Chunk4_5_checked, root6Node12Step1Chunk5_0_checked, root6Node12Step1Chunk5_1_checked, root6Node12Step1Chunk5_2_checked, root6Node12Step1Chunk5_3_checked, root6Node12Step1Chunk5_4_checked, root6Node12Step1Chunk5_5_checked, root6Node12Step1Chunk6_0_checked, root6Node12Step1Chunk6_1_checked, root6Node12Step1Chunk6_2_checked, root6Node12Step1Chunk6_3_checked, root6Node12Step1Chunk6_4_checked, root6Node12Step1Chunk6_5_checked, root6Node12Step1Chunk7_0_checked, root6Node12Step1Chunk7_1_checked, root6Node12Step1Chunk7_2_checked, root6Node12Step1Chunk7_3_checked, root6Node12Step1Chunk7_4_checked, root6Node12Step1Chunk7_5_checked, root6Node12Step1Chunk8_0_checked, root6Node12Step1Chunk8_1_checked, root6Node12Step1Chunk8_2_checked, root6Node12Step1Chunk8_3_checked, root6Node12Step1Chunk8_4_checked, root6Node12Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node12Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(5,0),(8,0)]
  | 4 => [(4,5),(7,3)]
  | 5 => [(4,1),(8,1)]
  | 6 => [(6,5)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
  | 9 => [(0,0),(6,4)]
  | 10 => [(1,2),(7,2)]
  | 11 => [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => [(5,5)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(1,5),(3,5)]
  | 16 => [(0,3),(6,1)]
  | 17 => [(4,1)]
  | 18 => [(0,1),(1,4),(6,5)]
  | 19 => [(0,5)]
  | 20 => [(4,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(2,0),(2,4)]
  | 24 => [(1,3),(7,3)]
  | 25 => [(5,2)]
  | 26 => [(2,5),(4,5),(7,5),(8,5)]
  | 27 => [(1,0),(6,0),(7,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(3,1),(7,1)]
  | 32 => [(0,1),(6,5)]
  | 33 => [(0,4),(6,2)]
  | 34 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(8,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(1,0),(7,0)]
  | 42 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => [(5,1),(5,4),(8,4)]
  | 44 => [(0,1),(6,4)]
  | 45 => [(1,2),(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(4,0),(7,4)]
  | 50 => [(7,5),(8,5)]
  | 51 => [(0,3),(1,0)]
  | 52 => [(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1),(8,1)]
  | 56 => [(4,2),(8,2)]
  | 57 => [(5,0),(5,3)]
  | 58 => [(4,5),(5,5),(8,5)]
  | 59 => [(7,0)]
  | _ => [(8,3)]
def root6Node12Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0),(8,0)]
  | 4 => some [(4,5),(7,3)]
  | 5 => some [(4,1),(8,1)]
  | 6 => some [(6,5)]
  | 7 => some [(0,4)]
  | 8 => some [(5,4)]
  | 9 => some [(0,0),(6,4)]
  | 10 => some [(1,2),(7,2)]
  | 11 => some [(1,3),(3,3),(5,3),(7,3),(8,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(1,5),(3,5)]
  | 16 => some [(0,3),(6,1)]
  | 17 => some [(4,1)]
  | 18 => some [(0,1),(1,4),(6,5)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,0),(2,4)]
  | 24 => some [(1,3),(7,3)]
  | 25 => some [(5,2)]
  | 26 => some [(2,5),(4,5),(7,5),(8,5)]
  | 27 => some [(1,0),(6,0),(7,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(3,1),(7,1)]
  | 32 => some [(0,1),(6,5)]
  | 33 => some [(0,4),(6,2)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(1,0),(7,0)]
  | 42 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => some [(5,1),(5,4),(8,4)]
  | 44 => some [(0,1),(6,4)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(4,0),(7,4)]
  | 50 => some [(7,5),(8,5)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1),(8,1)]
  | 56 => some [(4,2),(8,2)]
  | 57 => some [(5,0),(5,3)]
  | 58 => some [(4,5),(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node12Domains2_fast_eq : root6Node12Domains2 = expandDomains root6Node12Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node12Domains2 v = expandDomains root6Node12Domains2Fast v from by decide) v
theorem root6Node12Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root6Node12Domains1 root6Node12Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains1 root6Node12Domains2
    root6Node12Domains1Fast root6Node12Domains2Fast
    root6Node12Domains1_fast_eq root6Node12Domains2_fast_eq (by decide)
theorem root6Node12Step2_checked :
    checkReplacement table46 root6Node12Domains1 root6Node12Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node12Step2Chunk0_0_checked, root6Node12Step2Chunk0_1_checked, root6Node12Step2Chunk0_2_checked, root6Node12Step2Chunk0_3_checked, root6Node12Step2Chunk0_4_checked, root6Node12Step2Chunk0_5_checked, root6Node12Step2Chunk1_0_checked, root6Node12Step2Chunk1_1_checked, root6Node12Step2Chunk1_2_checked, root6Node12Step2Chunk1_3_checked, root6Node12Step2Chunk1_4_checked, root6Node12Step2Chunk1_5_checked, root6Node12Step2Chunk2_0_checked, root6Node12Step2Chunk2_1_checked, root6Node12Step2Chunk2_2_checked, root6Node12Step2Chunk2_3_checked, root6Node12Step2Chunk2_4_checked, root6Node12Step2Chunk2_5_checked, root6Node12Step2Chunk3_0_checked, root6Node12Step2Chunk3_1_checked, root6Node12Step2Chunk3_2_checked, root6Node12Step2Chunk3_3_checked, root6Node12Step2Chunk3_4_checked, root6Node12Step2Chunk3_5_checked, root6Node12Step2Chunk4_0_checked, root6Node12Step2Chunk4_1_checked, root6Node12Step2Chunk4_2_checked, root6Node12Step2Chunk4_3_checked, root6Node12Step2Chunk4_4_checked, root6Node12Step2Chunk4_5_checked, root6Node12Step2Chunk5_0_checked, root6Node12Step2Chunk5_1_checked, root6Node12Step2Chunk5_2_checked, root6Node12Step2Chunk5_3_checked, root6Node12Step2Chunk5_4_checked, root6Node12Step2Chunk5_5_checked, root6Node12Step2Chunk6_0_checked, root6Node12Step2Chunk6_1_checked, root6Node12Step2Chunk6_2_checked, root6Node12Step2Chunk6_3_checked, root6Node12Step2Chunk6_4_checked, root6Node12Step2Chunk6_5_checked, root6Node12Step2Chunk7_0_checked, root6Node12Step2Chunk7_1_checked, root6Node12Step2Chunk7_2_checked, root6Node12Step2Chunk7_3_checked, root6Node12Step2Chunk7_4_checked, root6Node12Step2Chunk7_5_checked, root6Node12Step2Chunk8_0_checked, root6Node12Step2Chunk8_1_checked, root6Node12Step2Chunk8_2_checked, root6Node12Step2Chunk8_3_checked, root6Node12Step2Chunk8_4_checked, root6Node12Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node12Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(5,0),(8,0)]
  | 4 => [(4,5),(7,3)]
  | 5 => [(8,1)]
  | 6 => [(6,5)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
  | 9 => [(0,0),(6,4)]
  | 10 => [(1,2),(7,2)]
  | 11 => [(5,3),(8,3)]
  | 12 => [(5,5)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(1,5),(3,5)]
  | 16 => [(0,3),(6,1)]
  | 17 => [(4,1)]
  | 18 => [(1,4)]
  | 19 => [(0,5)]
  | 20 => [(4,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(2,0),(2,4)]
  | 24 => [(1,3),(7,3)]
  | 25 => [(5,2)]
  | 26 => [(2,5),(7,5)]
  | 27 => [(6,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(3,1),(7,1)]
  | 32 => [(0,1),(6,5)]
  | 33 => [(0,4),(6,2)]
  | 34 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(8,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(1,0),(7,0)]
  | 42 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => [(5,1),(5,4),(8,4)]
  | 44 => [(0,1),(6,4)]
  | 45 => [(1,2),(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(4,0),(7,4)]
  | 50 => [(7,5),(8,5)]
  | 51 => [(0,3),(1,0)]
  | 52 => [(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1),(8,1)]
  | 56 => [(4,2),(8,2)]
  | 57 => [(5,0),(5,3)]
  | 58 => [(4,5),(5,5),(8,5)]
  | 59 => [(7,0)]
  | _ => [(8,3)]
def root6Node12Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0),(8,0)]
  | 4 => some [(4,5),(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(6,5)]
  | 7 => some [(0,4)]
  | 8 => some [(5,4)]
  | 9 => some [(0,0),(6,4)]
  | 10 => some [(1,2),(7,2)]
  | 11 => some [(5,3),(8,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(1,5),(3,5)]
  | 16 => some [(0,3),(6,1)]
  | 17 => some [(4,1)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,0),(2,4)]
  | 24 => some [(1,3),(7,3)]
  | 25 => some [(5,2)]
  | 26 => some [(2,5),(7,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(3,1),(7,1)]
  | 32 => some [(0,1),(6,5)]
  | 33 => some [(0,4),(6,2)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(1,0),(7,0)]
  | 42 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => some [(5,1),(5,4),(8,4)]
  | 44 => some [(0,1),(6,4)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(4,0),(7,4)]
  | 50 => some [(7,5),(8,5)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1),(8,1)]
  | 56 => some [(4,2),(8,2)]
  | 57 => some [(5,0),(5,3)]
  | 58 => some [(4,5),(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node12Domains3_fast_eq : root6Node12Domains3 = expandDomains root6Node12Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node12Domains3 v = expandDomains root6Node12Domains3Fast v from by decide) v
theorem root6Node12Step3Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root6Node12Domains2 root6Node12Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains2 root6Node12Domains3
    root6Node12Domains2Fast root6Node12Domains3Fast
    root6Node12Domains2_fast_eq root6Node12Domains3_fast_eq (by decide)
theorem root6Node12Step3_checked :
    checkReplacement table5 root6Node12Domains2 root6Node12Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node12Step3Chunk0_0_checked, root6Node12Step3Chunk0_1_checked, root6Node12Step3Chunk0_2_checked, root6Node12Step3Chunk0_3_checked, root6Node12Step3Chunk0_4_checked, root6Node12Step3Chunk0_5_checked, root6Node12Step3Chunk1_0_checked, root6Node12Step3Chunk1_1_checked, root6Node12Step3Chunk1_2_checked, root6Node12Step3Chunk1_3_checked, root6Node12Step3Chunk1_4_checked, root6Node12Step3Chunk1_5_checked, root6Node12Step3Chunk2_0_checked, root6Node12Step3Chunk2_1_checked, root6Node12Step3Chunk2_2_checked, root6Node12Step3Chunk2_3_checked, root6Node12Step3Chunk2_4_checked, root6Node12Step3Chunk2_5_checked, root6Node12Step3Chunk3_0_checked, root6Node12Step3Chunk3_1_checked, root6Node12Step3Chunk3_2_checked, root6Node12Step3Chunk3_3_checked, root6Node12Step3Chunk3_4_checked, root6Node12Step3Chunk3_5_checked, root6Node12Step3Chunk4_0_checked, root6Node12Step3Chunk4_1_checked, root6Node12Step3Chunk4_2_checked, root6Node12Step3Chunk4_3_checked, root6Node12Step3Chunk4_4_checked, root6Node12Step3Chunk4_5_checked, root6Node12Step3Chunk5_0_checked, root6Node12Step3Chunk5_1_checked, root6Node12Step3Chunk5_2_checked, root6Node12Step3Chunk5_3_checked, root6Node12Step3Chunk5_4_checked, root6Node12Step3Chunk5_5_checked, root6Node12Step3Chunk6_0_checked, root6Node12Step3Chunk6_1_checked, root6Node12Step3Chunk6_2_checked, root6Node12Step3Chunk6_3_checked, root6Node12Step3Chunk6_4_checked, root6Node12Step3Chunk6_5_checked, root6Node12Step3Chunk7_0_checked, root6Node12Step3Chunk7_1_checked, root6Node12Step3Chunk7_2_checked, root6Node12Step3Chunk7_3_checked, root6Node12Step3Chunk7_4_checked, root6Node12Step3Chunk7_5_checked, root6Node12Step3Chunk8_0_checked, root6Node12Step3Chunk8_1_checked, root6Node12Step3Chunk8_2_checked, root6Node12Step3Chunk8_3_checked, root6Node12Step3Chunk8_4_checked, root6Node12Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node12Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,4)]
  | 1 => [(1,3)]
  | 2 => [(8,2)]
  | 3 => [(5,0),(8,0)]
  | 4 => [(4,5),(7,3)]
  | 5 => [(8,1)]
  | 6 => [(6,5)]
  | 7 => [(0,4)]
  | 8 => [(5,4)]
  | 9 => [(0,0),(6,4)]
  | 10 => [(1,2),(7,2)]
  | 11 => [(5,3),(8,3)]
  | 12 => [(5,5)]
  | 13 => [(7,0)]
  | 14 => [(4,3)]
  | 15 => [(1,5),(3,5)]
  | 16 => [(0,3),(6,1)]
  | 17 => [(4,1)]
  | 18 => [(1,4)]
  | 19 => [(0,5)]
  | 20 => [(4,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(2,0),(2,4)]
  | 24 => [(1,3),(7,3)]
  | 25 => [(5,2)]
  | 26 => [(2,5),(7,5)]
  | 27 => [(6,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(3,1),(7,1)]
  | 32 => [(0,1),(6,5)]
  | 33 => [(0,4),(6,2)]
  | 34 => [(5,4),(8,4)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0),(8,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(1,0),(7,0)]
  | 42 => [(4,3),(7,1)]
  | 43 => [(5,1),(5,4),(8,4)]
  | 44 => [(0,1),(6,4)]
  | 45 => [(1,2),(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(4,0),(7,4)]
  | 50 => [(7,5),(8,5)]
  | 51 => [(0,3),(1,0)]
  | 52 => [(7,1),(8,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(5,1),(8,1)]
  | 56 => [(4,2),(8,2)]
  | 57 => [(5,0),(5,3)]
  | 58 => [(4,5),(5,5),(8,5)]
  | 59 => [(7,0)]
  | _ => [(8,3)]
def root6Node12Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,4)]
  | 1 => some [(1,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0),(8,0)]
  | 4 => some [(4,5),(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(6,5)]
  | 7 => some [(0,4)]
  | 8 => some [(5,4)]
  | 9 => some [(0,0),(6,4)]
  | 10 => some [(1,2),(7,2)]
  | 11 => some [(5,3),(8,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3)]
  | 15 => some [(1,5),(3,5)]
  | 16 => some [(0,3),(6,1)]
  | 17 => some [(4,1)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(2,0),(2,4)]
  | 24 => some [(1,3),(7,3)]
  | 25 => some [(5,2)]
  | 26 => some [(2,5),(7,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(3,1),(7,1)]
  | 32 => some [(0,1),(6,5)]
  | 33 => some [(0,4),(6,2)]
  | 34 => some [(5,4),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0),(8,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(1,0),(7,0)]
  | 42 => some [(4,3),(7,1)]
  | 43 => some [(5,1),(5,4),(8,4)]
  | 44 => some [(0,1),(6,4)]
  | 45 => some [(1,2),(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(4,0),(7,4)]
  | 50 => some [(7,5),(8,5)]
  | 51 => some [(0,3),(1,0)]
  | 52 => some [(7,1),(8,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(5,1),(8,1)]
  | 56 => some [(4,2),(8,2)]
  | 57 => some [(5,0),(5,3)]
  | 58 => some [(4,5),(5,5),(8,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node12Domains4_fast_eq : root6Node12Domains4 = expandDomains root6Node12Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node12Domains4 v = expandDomains root6Node12Domains4Fast v from by decide) v
theorem root6Node12Step4Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root6Node12Domains3 root6Node12Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node12Domains3 root6Node12Domains4
    root6Node12Domains3Fast root6Node12Domains4Fast
    root6Node12Domains3_fast_eq root6Node12Domains4_fast_eq (by decide)
theorem root6Node12Step4_checked :
    checkReplacement table16 root6Node12Domains3 root6Node12Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node12Step4Chunk0_0_checked, root6Node12Step4Chunk0_1_checked, root6Node12Step4Chunk0_2_checked, root6Node12Step4Chunk0_3_checked, root6Node12Step4Chunk0_4_checked, root6Node12Step4Chunk0_5_checked, root6Node12Step4Chunk1_0_checked, root6Node12Step4Chunk1_1_checked, root6Node12Step4Chunk1_2_checked, root6Node12Step4Chunk1_3_checked, root6Node12Step4Chunk1_4_checked, root6Node12Step4Chunk1_5_checked, root6Node12Step4Chunk2_0_checked, root6Node12Step4Chunk2_1_checked, root6Node12Step4Chunk2_2_checked, root6Node12Step4Chunk2_3_checked, root6Node12Step4Chunk2_4_checked, root6Node12Step4Chunk2_5_checked, root6Node12Step4Chunk3_0_checked, root6Node12Step4Chunk3_1_checked, root6Node12Step4Chunk3_2_checked, root6Node12Step4Chunk3_3_checked, root6Node12Step4Chunk3_4_checked, root6Node12Step4Chunk3_5_checked, root6Node12Step4Chunk4_0_checked, root6Node12Step4Chunk4_1_checked, root6Node12Step4Chunk4_2_checked, root6Node12Step4Chunk4_3_checked, root6Node12Step4Chunk4_4_checked, root6Node12Step4Chunk4_5_checked, root6Node12Step4Chunk5_0_checked, root6Node12Step4Chunk5_1_checked, root6Node12Step4Chunk5_2_checked, root6Node12Step4Chunk5_3_checked, root6Node12Step4Chunk5_4_checked, root6Node12Step4Chunk5_5_checked, root6Node12Step4Chunk6_0_checked, root6Node12Step4Chunk6_1_checked, root6Node12Step4Chunk6_2_checked, root6Node12Step4Chunk6_3_checked, root6Node12Step4Chunk6_4_checked, root6Node12Step4Chunk6_5_checked, root6Node12Step4Chunk7_0_checked, root6Node12Step4Chunk7_1_checked, root6Node12Step4Chunk7_2_checked, root6Node12Step4Chunk7_3_checked, root6Node12Step4Chunk7_4_checked, root6Node12Step4Chunk7_5_checked, root6Node12Step4Chunk8_0_checked, root6Node12Step4Chunk8_1_checked, root6Node12Step4Chunk8_2_checked, root6Node12Step4Chunk8_3_checked, root6Node12Step4Chunk8_4_checked, root6Node12Step4Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
