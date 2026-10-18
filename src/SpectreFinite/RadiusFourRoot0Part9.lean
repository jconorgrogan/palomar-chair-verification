module

public import SpectreFinite.RadiusFourRoot0Part8
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable0
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node24Domains0 : Domains 61 State := restrict root0Node12Domains3 19 (7,3)
def root0Node24Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1),(4,5)]
  | 5 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 6 => some [(0,1),(1,4),(7,4)]
  | 7 => some [(0,5),(6,2),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4),(8,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(4,3),(5,3),(7,1),(8,3)]
  | 12 => some [(4,1),(7,5),(8,5)]
  | 13 => some [(0,2),(1,0),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,1),(8,4)]
  | 18 => some [(4,0),(7,4),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,1),(8,4)]
  | 27 => some [(0,1),(6,4),(6,5)]
  | 28 => some [(0,4),(1,2),(6,2)]
  | 29 => some [(5,4),(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(6,3),(7,3)]
  | 34 => some [(4,2),(7,2),(8,2)]
  | 35 => some [(5,5),(7,5),(8,5)]
  | 36 => some [(0,3),(1,0),(7,0)]
  | 37 => some [(4,3),(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1),(5,1),(8,1)]
  | 41 => some [(0,1),(0,2),(6,5)]
  | 42 => some [(0,4),(1,1),(6,2)]
  | 43 => some [(4,2),(4,4),(8,2)]
  | 44 => some [(1,4),(5,0),(5,3)]
  | 45 => some [(0,5),(4,5),(5,5),(8,5)]
  | 46 => some [(2,0),(7,0)]
  | 47 => some [(7,3),(8,3)]
  | 48 => some [(5,2),(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0),(8,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4),(7,5)]
  | 51 => some [(0,0),(0,5),(6,0),(6,3)]
  | 52 => some [(3,1),(4,4),(7,2)]
  | 53 => some [(0,1),(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,2),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2),(8,4)]
  | 56 => some [(0,2),(1,5),(6,0),(8,2)]
  | 57 => some [(1,1),(5,0),(6,1),(7,1)]
  | 58 => some [(4,1),(4,5),(7,5),(8,1)]
  | 59 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node24Domains0_fast_eq : root0Node24Domains0 = expandDomains root0Node24Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node24Domains0 v = expandDomains root0Node24Domains0Fast v from by decide) v
def root0Node24Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0),(7,0),(8,0)]
  | 1 => [(4,3),(7,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => [(2,1),(2,5),(4,1),(4,5)]
  | 5 => [(4,4),(7,2),(8,4)]
  | 6 => [(1,4),(7,4)]
  | 7 => [(0,5),(6,3)]
  | 8 => [(2,0),(2,2),(2,4),(4,4)]
  | 9 => [(0,0),(1,3),(3,3),(7,3)]
  | 10 => [(3,2),(5,2),(7,2)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(7,5)]
  | 13 => [(0,2),(6,0)]
  | 14 => [(1,1),(3,1),(7,1)]
  | 15 => [(0,1),(1,5),(6,5)]
  | 16 => [(0,4),(6,1),(6,2)]
  | 17 => [(5,1),(5,4),(8,1),(8,4)]
  | 18 => [(4,0),(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2),(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0),(7,0)]
  | 24 => [(4,3),(7,1),(8,3)]
  | 25 => [(7,5),(8,5)]
  | 26 => [(5,1),(5,4),(8,4)]
  | 27 => [(0,1),(6,4)]
  | 28 => [(1,2),(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0),(7,4)]
  | 33 => [(1,3),(6,3),(7,3)]
  | 34 => [(4,2),(7,2),(8,2)]
  | 35 => [(7,5),(8,5)]
  | 36 => [(0,3),(1,0)]
  | 37 => [(7,1),(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1),(8,1)]
  | 41 => [(0,1),(0,2),(6,5)]
  | 42 => [(0,4),(1,1),(6,2)]
  | 43 => [(4,2),(8,2)]
  | 44 => [(5,0),(5,3)]
  | 45 => [(4,5),(5,5),(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,2),(5,5),(8,5)]
  | 49 => [(1,0),(3,0),(7,0),(8,0)]
  | 50 => [(1,4),(3,4),(5,4),(7,4)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,2),(6,3)]
  | 55 => [(4,4),(7,2),(8,2),(8,4)]
  | 56 => [(0,2),(1,5),(6,0),(8,2)]
  | 57 => [(1,1),(5,0),(6,1),(7,1)]
  | 58 => [(4,1),(4,5),(7,5),(8,1)]
  | 59 => [(0,2),(1,0),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node24Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,2),(5,5),(7,5),(8,2)]
  | 3 => some [(0,3),(1,0),(3,0),(5,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1),(4,5)]
  | 5 => some [(4,4),(7,2),(8,4)]
  | 6 => some [(1,4),(7,4)]
  | 7 => some [(0,5),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(7,5)]
  | 13 => some [(0,2),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,1),(8,4)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(6,3),(7,3)]
  | 34 => some [(4,2),(7,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1),(8,1)]
  | 41 => some [(0,1),(0,2),(6,5)]
  | 42 => some [(0,4),(1,1),(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,2),(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0),(8,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,2),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2),(8,4)]
  | 56 => some [(0,2),(1,5),(6,0),(8,2)]
  | 57 => some [(1,1),(5,0),(6,1),(7,1)]
  | 58 => some [(4,1),(4,5),(7,5),(8,1)]
  | 59 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node24Domains1_fast_eq : root0Node24Domains1 = expandDomains root0Node24Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node24Domains1 v = expandDomains root0Node24Domains1Fast v from by decide) v
theorem root0Node24Step1Chunk0_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk0_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk0_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk0_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk0_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk0_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk1_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk2_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk3_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk4_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk5_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk6_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk7_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_0⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_1⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_2⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_3⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_4⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1Chunk8_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_5⟩
      root0Node24Domains0 root0Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains0 root0Node24Domains1
    root0Node24Domains0Fast root0Node24Domains1Fast
    root0Node24Domains0_fast_eq root0Node24Domains1_fast_eq (by decide)
theorem root0Node24Step1_checked :
    checkReplacement table29 root0Node24Domains0 root0Node24Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node24Step1Chunk0_0_checked, root0Node24Step1Chunk0_1_checked, root0Node24Step1Chunk0_2_checked, root0Node24Step1Chunk0_3_checked, root0Node24Step1Chunk0_4_checked, root0Node24Step1Chunk0_5_checked, root0Node24Step1Chunk1_0_checked, root0Node24Step1Chunk1_1_checked, root0Node24Step1Chunk1_2_checked, root0Node24Step1Chunk1_3_checked, root0Node24Step1Chunk1_4_checked, root0Node24Step1Chunk1_5_checked, root0Node24Step1Chunk2_0_checked, root0Node24Step1Chunk2_1_checked, root0Node24Step1Chunk2_2_checked, root0Node24Step1Chunk2_3_checked, root0Node24Step1Chunk2_4_checked, root0Node24Step1Chunk2_5_checked, root0Node24Step1Chunk3_0_checked, root0Node24Step1Chunk3_1_checked, root0Node24Step1Chunk3_2_checked, root0Node24Step1Chunk3_3_checked, root0Node24Step1Chunk3_4_checked, root0Node24Step1Chunk3_5_checked, root0Node24Step1Chunk4_0_checked, root0Node24Step1Chunk4_1_checked, root0Node24Step1Chunk4_2_checked, root0Node24Step1Chunk4_3_checked, root0Node24Step1Chunk4_4_checked, root0Node24Step1Chunk4_5_checked, root0Node24Step1Chunk5_0_checked, root0Node24Step1Chunk5_1_checked, root0Node24Step1Chunk5_2_checked, root0Node24Step1Chunk5_3_checked, root0Node24Step1Chunk5_4_checked, root0Node24Step1Chunk5_5_checked, root0Node24Step1Chunk6_0_checked, root0Node24Step1Chunk6_1_checked, root0Node24Step1Chunk6_2_checked, root0Node24Step1Chunk6_3_checked, root0Node24Step1Chunk6_4_checked, root0Node24Step1Chunk6_5_checked, root0Node24Step1Chunk7_0_checked, root0Node24Step1Chunk7_1_checked, root0Node24Step1Chunk7_2_checked, root0Node24Step1Chunk7_3_checked, root0Node24Step1Chunk7_4_checked, root0Node24Step1Chunk7_5_checked, root0Node24Step1Chunk8_0_checked, root0Node24Step1Chunk8_1_checked, root0Node24Step1Chunk8_2_checked, root0Node24Step1Chunk8_3_checked, root0Node24Step1Chunk8_4_checked, root0Node24Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node24Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0),(7,0),(8,0)]
  | 1 => [(4,3),(7,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(7,5)]
  | 3 => [(0,3),(1,0),(3,0),(6,1)]
  | 4 => [(2,1),(2,5),(4,1)]
  | 5 => [(4,4),(7,2),(8,4)]
  | 6 => [(1,4),(7,4)]
  | 7 => [(0,5),(6,3)]
  | 8 => [(2,0),(2,2),(2,4),(4,4)]
  | 9 => [(0,0),(1,3),(3,3),(7,3)]
  | 10 => [(3,2),(5,2),(7,2)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(7,5)]
  | 13 => [(0,2),(6,0)]
  | 14 => [(1,1),(3,1),(7,1)]
  | 15 => [(0,1),(1,5),(6,5)]
  | 16 => [(0,4),(6,1),(6,2)]
  | 17 => [(5,1),(5,4),(8,4)]
  | 18 => [(4,0),(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2),(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0),(7,0)]
  | 24 => [(4,3),(7,1),(8,3)]
  | 25 => [(7,5),(8,5)]
  | 26 => [(5,1),(5,4),(8,4)]
  | 27 => [(0,1),(6,4)]
  | 28 => [(1,2),(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0),(7,4)]
  | 33 => [(1,3),(7,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5),(8,5)]
  | 36 => [(0,3),(1,0)]
  | 37 => [(7,1),(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1),(8,1)]
  | 41 => [(0,1),(6,5)]
  | 42 => [(0,4),(6,2)]
  | 43 => [(4,2),(8,2)]
  | 44 => [(5,0),(5,3)]
  | 45 => [(4,5),(5,5),(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(1,0),(3,0),(7,0)]
  | 50 => [(1,4),(3,4),(5,4),(7,4)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,2),(6,3)]
  | 55 => [(4,4),(7,2),(8,2),(8,4)]
  | 56 => [(0,2),(1,5),(6,0),(8,2)]
  | 57 => [(1,1),(5,0),(6,1),(7,1)]
  | 58 => [(4,1),(4,5),(7,5),(8,1)]
  | 59 => [(0,2),(1,0),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node24Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1)]
  | 5 => some [(4,4),(7,2),(8,4)]
  | 6 => some [(1,4),(7,4)]
  | 7 => some [(0,5),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(7,5)]
  | 13 => some [(0,2),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,4)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1),(8,1)]
  | 41 => some [(0,1),(6,5)]
  | 42 => some [(0,4),(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,2),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2),(8,4)]
  | 56 => some [(0,2),(1,5),(6,0),(8,2)]
  | 57 => some [(1,1),(5,0),(6,1),(7,1)]
  | 58 => some [(4,1),(4,5),(7,5),(8,1)]
  | 59 => some [(0,2),(1,0),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node24Domains2_fast_eq : root0Node24Domains2 = expandDomains root0Node24Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node24Domains2 v = expandDomains root0Node24Domains2Fast v from by decide) v
theorem root0Node24Step2Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root0Node24Domains1 root0Node24Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains1 root0Node24Domains2
    root0Node24Domains1Fast root0Node24Domains2Fast
    root0Node24Domains1_fast_eq root0Node24Domains2_fast_eq (by decide)
theorem root0Node24Step2_checked :
    checkReplacement table23 root0Node24Domains1 root0Node24Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node24Step2Chunk0_0_checked, root0Node24Step2Chunk0_1_checked, root0Node24Step2Chunk0_2_checked, root0Node24Step2Chunk0_3_checked, root0Node24Step2Chunk0_4_checked, root0Node24Step2Chunk0_5_checked, root0Node24Step2Chunk1_0_checked, root0Node24Step2Chunk1_1_checked, root0Node24Step2Chunk1_2_checked, root0Node24Step2Chunk1_3_checked, root0Node24Step2Chunk1_4_checked, root0Node24Step2Chunk1_5_checked, root0Node24Step2Chunk2_0_checked, root0Node24Step2Chunk2_1_checked, root0Node24Step2Chunk2_2_checked, root0Node24Step2Chunk2_3_checked, root0Node24Step2Chunk2_4_checked, root0Node24Step2Chunk2_5_checked, root0Node24Step2Chunk3_0_checked, root0Node24Step2Chunk3_1_checked, root0Node24Step2Chunk3_2_checked, root0Node24Step2Chunk3_3_checked, root0Node24Step2Chunk3_4_checked, root0Node24Step2Chunk3_5_checked, root0Node24Step2Chunk4_0_checked, root0Node24Step2Chunk4_1_checked, root0Node24Step2Chunk4_2_checked, root0Node24Step2Chunk4_3_checked, root0Node24Step2Chunk4_4_checked, root0Node24Step2Chunk4_5_checked, root0Node24Step2Chunk5_0_checked, root0Node24Step2Chunk5_1_checked, root0Node24Step2Chunk5_2_checked, root0Node24Step2Chunk5_3_checked, root0Node24Step2Chunk5_4_checked, root0Node24Step2Chunk5_5_checked, root0Node24Step2Chunk6_0_checked, root0Node24Step2Chunk6_1_checked, root0Node24Step2Chunk6_2_checked, root0Node24Step2Chunk6_3_checked, root0Node24Step2Chunk6_4_checked, root0Node24Step2Chunk6_5_checked, root0Node24Step2Chunk7_0_checked, root0Node24Step2Chunk7_1_checked, root0Node24Step2Chunk7_2_checked, root0Node24Step2Chunk7_3_checked, root0Node24Step2Chunk7_4_checked, root0Node24Step2Chunk7_5_checked, root0Node24Step2Chunk8_0_checked, root0Node24Step2Chunk8_1_checked, root0Node24Step2Chunk8_2_checked, root0Node24Step2Chunk8_3_checked, root0Node24Step2Chunk8_4_checked, root0Node24Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node24Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0),(7,0),(8,0)]
  | 1 => [(4,3),(7,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(7,5)]
  | 3 => [(0,3),(1,0),(3,0),(6,1)]
  | 4 => [(2,1),(2,5),(4,1)]
  | 5 => [(4,4),(7,2),(8,4)]
  | 6 => [(1,4),(7,4)]
  | 7 => [(0,5),(6,3)]
  | 8 => [(2,0),(2,2),(2,4),(4,4)]
  | 9 => [(0,0),(1,3),(3,3),(7,3)]
  | 10 => [(3,2),(5,2),(7,2)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(7,5)]
  | 13 => [(0,2),(6,0)]
  | 14 => [(1,1),(3,1),(7,1)]
  | 15 => [(0,1),(1,5),(6,5)]
  | 16 => [(0,4),(6,1),(6,2)]
  | 17 => [(5,1),(5,4),(8,4)]
  | 18 => [(4,0),(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2),(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0),(7,0)]
  | 24 => [(4,3),(7,1),(8,3)]
  | 25 => [(7,5),(8,5)]
  | 26 => [(5,1),(5,4),(8,4)]
  | 27 => [(0,1),(6,4)]
  | 28 => [(1,2),(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0),(7,4)]
  | 33 => [(1,3),(7,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5),(8,5)]
  | 36 => [(0,3),(1,0)]
  | 37 => [(7,1),(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1),(8,1)]
  | 41 => [(0,1),(6,5)]
  | 42 => [(0,4),(6,2)]
  | 43 => [(4,2),(8,2)]
  | 44 => [(5,0),(5,3)]
  | 45 => [(4,5),(5,5),(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(1,0),(3,0),(7,0)]
  | 50 => [(1,4),(3,4),(5,4),(7,4)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,3)]
  | 55 => [(4,4),(7,2),(8,2)]
  | 56 => [(0,2),(1,5),(6,0)]
  | 57 => [(1,1),(6,1),(7,1)]
  | 58 => [(4,1),(7,5),(8,1)]
  | 59 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node24Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0),(7,0),(8,0)]
  | 1 => some [(4,3),(7,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1)]
  | 5 => some [(4,4),(7,2),(8,4)]
  | 6 => some [(1,4),(7,4)]
  | 7 => some [(0,5),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(7,5)]
  | 13 => some [(0,2),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,4)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1),(8,1)]
  | 41 => some [(0,1),(6,5)]
  | 42 => some [(0,4),(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node24Domains3_fast_eq : root0Node24Domains3 = expandDomains root0Node24Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node24Domains3 v = expandDomains root0Node24Domains3Fast v from by decide) v
theorem root0Node24Step3Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root0Node24Domains2 root0Node24Domains3 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains2 root0Node24Domains3
    root0Node24Domains2Fast root0Node24Domains3Fast
    root0Node24Domains2_fast_eq root0Node24Domains3_fast_eq (by decide)
theorem root0Node24Step3_checked :
    checkReplacement table46 root0Node24Domains2 root0Node24Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node24Step3Chunk0_0_checked, root0Node24Step3Chunk0_1_checked, root0Node24Step3Chunk0_2_checked, root0Node24Step3Chunk0_3_checked, root0Node24Step3Chunk0_4_checked, root0Node24Step3Chunk0_5_checked, root0Node24Step3Chunk1_0_checked, root0Node24Step3Chunk1_1_checked, root0Node24Step3Chunk1_2_checked, root0Node24Step3Chunk1_3_checked, root0Node24Step3Chunk1_4_checked, root0Node24Step3Chunk1_5_checked, root0Node24Step3Chunk2_0_checked, root0Node24Step3Chunk2_1_checked, root0Node24Step3Chunk2_2_checked, root0Node24Step3Chunk2_3_checked, root0Node24Step3Chunk2_4_checked, root0Node24Step3Chunk2_5_checked, root0Node24Step3Chunk3_0_checked, root0Node24Step3Chunk3_1_checked, root0Node24Step3Chunk3_2_checked, root0Node24Step3Chunk3_3_checked, root0Node24Step3Chunk3_4_checked, root0Node24Step3Chunk3_5_checked, root0Node24Step3Chunk4_0_checked, root0Node24Step3Chunk4_1_checked, root0Node24Step3Chunk4_2_checked, root0Node24Step3Chunk4_3_checked, root0Node24Step3Chunk4_4_checked, root0Node24Step3Chunk4_5_checked, root0Node24Step3Chunk5_0_checked, root0Node24Step3Chunk5_1_checked, root0Node24Step3Chunk5_2_checked, root0Node24Step3Chunk5_3_checked, root0Node24Step3Chunk5_4_checked, root0Node24Step3Chunk5_5_checked, root0Node24Step3Chunk6_0_checked, root0Node24Step3Chunk6_1_checked, root0Node24Step3Chunk6_2_checked, root0Node24Step3Chunk6_3_checked, root0Node24Step3Chunk6_4_checked, root0Node24Step3Chunk6_5_checked, root0Node24Step3Chunk7_0_checked, root0Node24Step3Chunk7_1_checked, root0Node24Step3Chunk7_2_checked, root0Node24Step3Chunk7_3_checked, root0Node24Step3Chunk7_4_checked, root0Node24Step3Chunk7_5_checked, root0Node24Step3Chunk8_0_checked, root0Node24Step3Chunk8_1_checked, root0Node24Step3Chunk8_2_checked, root0Node24Step3Chunk8_3_checked, root0Node24Step3Chunk8_4_checked, root0Node24Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node24Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0),(8,0)]
  | 1 => [(4,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(7,5)]
  | 3 => [(0,3),(1,0),(3,0),(6,1)]
  | 4 => [(2,1),(2,5),(4,1)]
  | 5 => [(4,4),(7,2),(8,4)]
  | 6 => [(1,4),(7,4)]
  | 7 => [(0,5),(6,3)]
  | 8 => [(2,0),(2,2),(2,4),(4,4)]
  | 9 => [(0,0),(1,3),(3,3),(7,3)]
  | 10 => [(3,2),(5,2),(7,2)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(7,5)]
  | 13 => [(0,2),(6,0)]
  | 14 => [(1,1),(3,1),(7,1)]
  | 15 => [(0,1),(1,5),(6,5)]
  | 16 => [(0,4),(6,1),(6,2)]
  | 17 => [(5,1),(5,4),(8,4)]
  | 18 => [(4,0),(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2),(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0),(7,0)]
  | 24 => [(4,3),(7,1),(8,3)]
  | 25 => [(7,5),(8,5)]
  | 26 => [(5,1),(5,4),(8,4)]
  | 27 => [(0,1),(6,4)]
  | 28 => [(1,2),(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0),(7,4)]
  | 33 => [(1,3),(7,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5),(8,5)]
  | 36 => [(0,3),(1,0)]
  | 37 => [(7,1),(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1),(8,1)]
  | 41 => [(0,1),(6,5)]
  | 42 => [(0,4),(6,2)]
  | 43 => [(4,2),(8,2)]
  | 44 => [(5,0),(5,3)]
  | 45 => [(4,5),(5,5),(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(1,0),(3,0),(7,0)]
  | 50 => [(1,4),(3,4),(5,4),(7,4)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,3)]
  | 55 => [(4,4),(7,2),(8,2)]
  | 56 => [(0,2),(1,5),(6,0)]
  | 57 => [(1,1),(6,1),(7,1)]
  | 58 => [(4,1),(7,5),(8,1)]
  | 59 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node24Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0),(8,0)]
  | 1 => some [(4,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1)]
  | 5 => some [(4,4),(7,2),(8,4)]
  | 6 => some [(1,4),(7,4)]
  | 7 => some [(0,5),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(7,5)]
  | 13 => some [(0,2),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,4)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1),(8,1)]
  | 41 => some [(0,1),(6,5)]
  | 42 => some [(0,4),(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node24Domains4_fast_eq : root0Node24Domains4 = expandDomains root0Node24Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node24Domains4 v = expandDomains root0Node24Domains4Fast v from by decide) v
theorem root0Node24Step4Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root0Node24Domains3 root0Node24Domains4 = true := by
  exact checkNarrowing_of_fast _ root0Node24Domains3 root0Node24Domains4
    root0Node24Domains3Fast root0Node24Domains4Fast
    root0Node24Domains3_fast_eq root0Node24Domains4_fast_eq (by decide)
theorem root0Node24Step4_checked :
    checkReplacement table0 root0Node24Domains3 root0Node24Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node24Step4Chunk0_0_checked, root0Node24Step4Chunk0_1_checked, root0Node24Step4Chunk0_2_checked, root0Node24Step4Chunk0_3_checked, root0Node24Step4Chunk0_4_checked, root0Node24Step4Chunk0_5_checked, root0Node24Step4Chunk1_0_checked, root0Node24Step4Chunk1_1_checked, root0Node24Step4Chunk1_2_checked, root0Node24Step4Chunk1_3_checked, root0Node24Step4Chunk1_4_checked, root0Node24Step4Chunk1_5_checked, root0Node24Step4Chunk2_0_checked, root0Node24Step4Chunk2_1_checked, root0Node24Step4Chunk2_2_checked, root0Node24Step4Chunk2_3_checked, root0Node24Step4Chunk2_4_checked, root0Node24Step4Chunk2_5_checked, root0Node24Step4Chunk3_0_checked, root0Node24Step4Chunk3_1_checked, root0Node24Step4Chunk3_2_checked, root0Node24Step4Chunk3_3_checked, root0Node24Step4Chunk3_4_checked, root0Node24Step4Chunk3_5_checked, root0Node24Step4Chunk4_0_checked, root0Node24Step4Chunk4_1_checked, root0Node24Step4Chunk4_2_checked, root0Node24Step4Chunk4_3_checked, root0Node24Step4Chunk4_4_checked, root0Node24Step4Chunk4_5_checked, root0Node24Step4Chunk5_0_checked, root0Node24Step4Chunk5_1_checked, root0Node24Step4Chunk5_2_checked, root0Node24Step4Chunk5_3_checked, root0Node24Step4Chunk5_4_checked, root0Node24Step4Chunk5_5_checked, root0Node24Step4Chunk6_0_checked, root0Node24Step4Chunk6_1_checked, root0Node24Step4Chunk6_2_checked, root0Node24Step4Chunk6_3_checked, root0Node24Step4Chunk6_4_checked, root0Node24Step4Chunk6_5_checked, root0Node24Step4Chunk7_0_checked, root0Node24Step4Chunk7_1_checked, root0Node24Step4Chunk7_2_checked, root0Node24Step4Chunk7_3_checked, root0Node24Step4Chunk7_4_checked, root0Node24Step4Chunk7_5_checked, root0Node24Step4Chunk8_0_checked, root0Node24Step4Chunk8_1_checked, root0Node24Step4Chunk8_2_checked, root0Node24Step4Chunk8_3_checked, root0Node24Step4Chunk8_4_checked, root0Node24Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node25Domains0 : Domains 61 State := restrict root0Node24Domains4 0 (7,0)
def root0Node25Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1)]
  | 5 => some [(4,4),(7,2),(8,4)]
  | 6 => some [(1,4),(7,4)]
  | 7 => some [(0,5),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(7,5)]
  | 13 => some [(0,2),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,4)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1),(8,1)]
  | 41 => some [(0,1),(6,5)]
  | 42 => some [(0,4),(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node25Domains0_fast_eq : root0Node25Domains0 = expandDomains root0Node25Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node25Domains0 v = expandDomains root0Node25Domains0Fast v from by decide) v
def root0Node25Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3),(8,3)]
  | 2 => [(1,5),(3,5),(5,5),(7,5)]
  | 3 => [(0,3),(1,0),(3,0),(6,1)]
  | 4 => [(2,1),(2,5),(4,1)]
  | 5 => [(4,4),(7,2)]
  | 6 => [(1,4),(7,4)]
  | 7 => [(0,5),(6,3)]
  | 8 => [(2,0),(2,2),(2,4),(4,4)]
  | 9 => [(0,0),(1,3),(3,3),(7,3)]
  | 10 => [(3,2),(5,2),(7,2)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(7,5)]
  | 13 => [(0,2),(6,0)]
  | 14 => [(1,1),(3,1),(7,1)]
  | 15 => [(0,1),(1,5),(6,5)]
  | 16 => [(0,4),(6,1),(6,2)]
  | 17 => [(5,1),(5,4),(8,4)]
  | 18 => [(4,0),(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2),(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0),(7,0)]
  | 24 => [(4,3),(7,1),(8,3)]
  | 25 => [(7,5),(8,5)]
  | 26 => [(5,1),(5,4),(8,4)]
  | 27 => [(0,1),(6,4)]
  | 28 => [(1,2),(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0),(7,4)]
  | 33 => [(1,3),(7,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5),(8,5)]
  | 36 => [(0,3),(1,0)]
  | 37 => [(7,1),(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1),(8,1)]
  | 41 => [(0,1),(6,5)]
  | 42 => [(0,4),(6,2)]
  | 43 => [(4,2),(8,2)]
  | 44 => [(5,0),(5,3)]
  | 45 => [(4,5),(5,5),(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(1,0),(3,0),(7,0)]
  | 50 => [(1,4),(3,4),(5,4),(7,4)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,3)]
  | 55 => [(4,4),(7,2),(8,2)]
  | 56 => [(0,2),(1,5),(6,0)]
  | 57 => [(1,1),(6,1),(7,1)]
  | 58 => [(4,1),(7,5),(8,1)]
  | 59 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node25Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3),(8,3)]
  | 2 => some [(1,5),(3,5),(5,5),(7,5)]
  | 3 => some [(0,3),(1,0),(3,0),(6,1)]
  | 4 => some [(2,1),(2,5),(4,1)]
  | 5 => some [(4,4),(7,2)]
  | 6 => some [(1,4),(7,4)]
  | 7 => some [(0,5),(6,3)]
  | 8 => some [(2,0),(2,2),(2,4),(4,4)]
  | 9 => some [(0,0),(1,3),(3,3),(7,3)]
  | 10 => some [(3,2),(5,2),(7,2)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(7,5)]
  | 13 => some [(0,2),(6,0)]
  | 14 => some [(1,1),(3,1),(7,1)]
  | 15 => some [(0,1),(1,5),(6,5)]
  | 16 => some [(0,4),(6,1),(6,2)]
  | 17 => some [(5,1),(5,4),(8,4)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1),(8,3)]
  | 25 => some [(7,5),(8,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1),(8,1)]
  | 41 => some [(0,1),(6,5)]
  | 42 => some [(0,4),(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node25Domains1_fast_eq : root0Node25Domains1 = expandDomains root0Node25Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node25Domains1 v = expandDomains root0Node25Domains1Fast v from by decide) v
theorem root0Node25Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root0Node25Domains0 root0Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node25Domains0 root0Node25Domains1
    root0Node25Domains0Fast root0Node25Domains1Fast
    root0Node25Domains0_fast_eq root0Node25Domains1_fast_eq (by decide)
theorem root0Node25Step1_checked :
    checkReplacement table0 root0Node25Domains0 root0Node25Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node25Step1Chunk0_0_checked, root0Node25Step1Chunk0_1_checked, root0Node25Step1Chunk0_2_checked, root0Node25Step1Chunk0_3_checked, root0Node25Step1Chunk0_4_checked, root0Node25Step1Chunk0_5_checked, root0Node25Step1Chunk1_0_checked, root0Node25Step1Chunk1_1_checked, root0Node25Step1Chunk1_2_checked, root0Node25Step1Chunk1_3_checked, root0Node25Step1Chunk1_4_checked, root0Node25Step1Chunk1_5_checked, root0Node25Step1Chunk2_0_checked, root0Node25Step1Chunk2_1_checked, root0Node25Step1Chunk2_2_checked, root0Node25Step1Chunk2_3_checked, root0Node25Step1Chunk2_4_checked, root0Node25Step1Chunk2_5_checked, root0Node25Step1Chunk3_0_checked, root0Node25Step1Chunk3_1_checked, root0Node25Step1Chunk3_2_checked, root0Node25Step1Chunk3_3_checked, root0Node25Step1Chunk3_4_checked, root0Node25Step1Chunk3_5_checked, root0Node25Step1Chunk4_0_checked, root0Node25Step1Chunk4_1_checked, root0Node25Step1Chunk4_2_checked, root0Node25Step1Chunk4_3_checked, root0Node25Step1Chunk4_4_checked, root0Node25Step1Chunk4_5_checked, root0Node25Step1Chunk5_0_checked, root0Node25Step1Chunk5_1_checked, root0Node25Step1Chunk5_2_checked, root0Node25Step1Chunk5_3_checked, root0Node25Step1Chunk5_4_checked, root0Node25Step1Chunk5_5_checked, root0Node25Step1Chunk6_0_checked, root0Node25Step1Chunk6_1_checked, root0Node25Step1Chunk6_2_checked, root0Node25Step1Chunk6_3_checked, root0Node25Step1Chunk6_4_checked, root0Node25Step1Chunk6_5_checked, root0Node25Step1Chunk7_0_checked, root0Node25Step1Chunk7_1_checked, root0Node25Step1Chunk7_2_checked, root0Node25Step1Chunk7_3_checked, root0Node25Step1Chunk7_4_checked, root0Node25Step1Chunk7_5_checked, root0Node25Step1Chunk8_0_checked, root0Node25Step1Chunk8_1_checked, root0Node25Step1Chunk8_2_checked, root0Node25Step1Chunk8_3_checked, root0Node25Step1Chunk8_4_checked, root0Node25Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
