module

public import SpectreFinite.RadiusFourRoot1Part8
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable40
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node25Domains0 : Domains 61 State := restrict root1Node24Domains1 17 (7,3)
def root1Node25Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(1,4),(6,4)]
  | 25 => some [(0,5),(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(6,0)]
  | 34 => some [(7,1),(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2),(8,2)]
  | 42 => some [(5,0),(5,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,1),(6,4)]
  | 48 => some [(1,2),(6,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0)]
  | 55 => some [(2,1),(4,1),(8,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(1,3),(6,3)]
  | 59 => some [(2,2),(2,4),(4,2),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(5,3)]
theorem root1Node25Domains0_fast_eq : root1Node25Domains0 = expandDomains root1Node25Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node25Domains0 v = expandDomains root1Node25Domains0Fast v from by decide) v
def root1Node25Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,3)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(1,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3),(6,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(4,1),(8,1)]
  | 44 => [(0,2),(6,5)]
  | 45 => [(0,4),(1,1)]
  | 46 => [(5,1),(5,4)]
  | 47 => [(0,1),(6,4)]
  | 48 => [(1,2),(6,2)]
  | 49 => [(7,4)]
  | 50 => [(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(3,5),(5,5),(7,5)]
  | 54 => [(0,3),(1,0)]
  | 55 => [(2,1),(4,1)]
  | 56 => [(4,4),(5,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(6,3)]
  | 59 => [(2,2),(2,4),(4,4)]
  | _ => [(0,0),(1,3),(3,3)]
def root1Node25Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,1),(6,4)]
  | 48 => some [(1,2),(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,2),(2,4),(4,4)]
  | _ => some [(0,0),(1,3),(3,3)]
theorem root1Node25Domains1_fast_eq : root1Node25Domains1 = expandDomains root1Node25Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node25Domains1 v = expandDomains root1Node25Domains1Fast v from by decide) v
theorem root1Node25Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root1Node25Domains0 root1Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node25Domains0 root1Node25Domains1
    root1Node25Domains0Fast root1Node25Domains1Fast
    root1Node25Domains0_fast_eq root1Node25Domains1_fast_eq (by decide)
theorem root1Node25Step1_checked :
    checkReplacement table40 root1Node25Domains0 root1Node25Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node25Step1Chunk0_0_checked, root1Node25Step1Chunk0_1_checked, root1Node25Step1Chunk0_2_checked, root1Node25Step1Chunk0_3_checked, root1Node25Step1Chunk0_4_checked, root1Node25Step1Chunk0_5_checked, root1Node25Step1Chunk1_0_checked, root1Node25Step1Chunk1_1_checked, root1Node25Step1Chunk1_2_checked, root1Node25Step1Chunk1_3_checked, root1Node25Step1Chunk1_4_checked, root1Node25Step1Chunk1_5_checked, root1Node25Step1Chunk2_0_checked, root1Node25Step1Chunk2_1_checked, root1Node25Step1Chunk2_2_checked, root1Node25Step1Chunk2_3_checked, root1Node25Step1Chunk2_4_checked, root1Node25Step1Chunk2_5_checked, root1Node25Step1Chunk3_0_checked, root1Node25Step1Chunk3_1_checked, root1Node25Step1Chunk3_2_checked, root1Node25Step1Chunk3_3_checked, root1Node25Step1Chunk3_4_checked, root1Node25Step1Chunk3_5_checked, root1Node25Step1Chunk4_0_checked, root1Node25Step1Chunk4_1_checked, root1Node25Step1Chunk4_2_checked, root1Node25Step1Chunk4_3_checked, root1Node25Step1Chunk4_4_checked, root1Node25Step1Chunk4_5_checked, root1Node25Step1Chunk5_0_checked, root1Node25Step1Chunk5_1_checked, root1Node25Step1Chunk5_2_checked, root1Node25Step1Chunk5_3_checked, root1Node25Step1Chunk5_4_checked, root1Node25Step1Chunk5_5_checked, root1Node25Step1Chunk6_0_checked, root1Node25Step1Chunk6_1_checked, root1Node25Step1Chunk6_2_checked, root1Node25Step1Chunk6_3_checked, root1Node25Step1Chunk6_4_checked, root1Node25Step1Chunk6_5_checked, root1Node25Step1Chunk7_0_checked, root1Node25Step1Chunk7_1_checked, root1Node25Step1Chunk7_2_checked, root1Node25Step1Chunk7_3_checked, root1Node25Step1Chunk7_4_checked, root1Node25Step1Chunk7_5_checked, root1Node25Step1Chunk8_0_checked, root1Node25Step1Chunk8_1_checked, root1Node25Step1Chunk8_2_checked, root1Node25Step1Chunk8_3_checked, root1Node25Step1Chunk8_4_checked, root1Node25Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node26Domains0 : Domains 61 State := restrict root1Node25Domains1 37 (1,3)
def root1Node26Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,1),(6,4)]
  | 48 => some [(1,2),(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,2),(2,4),(4,4)]
  | _ => some [(0,0),(1,3),(3,3)]
theorem root1Node26Domains0_fast_eq : root1Node26Domains0 = expandDomains root1Node26Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node26Domains0 v = expandDomains root1Node26Domains0Fast v from by decide) v
def root1Node26Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,3)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(1,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5),(8,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(3,5),(7,5)]
  | 54 => [(0,3)]
  | 55 => [(4,1)]
  | 56 => [(4,4),(7,2)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(6,3)]
  | 59 => [(2,2),(2,4)]
  | _ => [(1,3),(3,3)]
def root1Node26Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(3,5),(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,2),(2,4)]
  | _ => some [(1,3),(3,3)]
theorem root1Node26Domains1_fast_eq : root1Node26Domains1 = expandDomains root1Node26Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node26Domains1 v = expandDomains root1Node26Domains1Fast v from by decide) v
theorem root1Node26Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root1Node26Domains0 root1Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node26Domains0 root1Node26Domains1
    root1Node26Domains0Fast root1Node26Domains1Fast
    root1Node26Domains0_fast_eq root1Node26Domains1_fast_eq (by decide)
theorem root1Node26Step1_checked :
    checkReplacement table46 root1Node26Domains0 root1Node26Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node26Step1Chunk0_0_checked, root1Node26Step1Chunk0_1_checked, root1Node26Step1Chunk0_2_checked, root1Node26Step1Chunk0_3_checked, root1Node26Step1Chunk0_4_checked, root1Node26Step1Chunk0_5_checked, root1Node26Step1Chunk1_0_checked, root1Node26Step1Chunk1_1_checked, root1Node26Step1Chunk1_2_checked, root1Node26Step1Chunk1_3_checked, root1Node26Step1Chunk1_4_checked, root1Node26Step1Chunk1_5_checked, root1Node26Step1Chunk2_0_checked, root1Node26Step1Chunk2_1_checked, root1Node26Step1Chunk2_2_checked, root1Node26Step1Chunk2_3_checked, root1Node26Step1Chunk2_4_checked, root1Node26Step1Chunk2_5_checked, root1Node26Step1Chunk3_0_checked, root1Node26Step1Chunk3_1_checked, root1Node26Step1Chunk3_2_checked, root1Node26Step1Chunk3_3_checked, root1Node26Step1Chunk3_4_checked, root1Node26Step1Chunk3_5_checked, root1Node26Step1Chunk4_0_checked, root1Node26Step1Chunk4_1_checked, root1Node26Step1Chunk4_2_checked, root1Node26Step1Chunk4_3_checked, root1Node26Step1Chunk4_4_checked, root1Node26Step1Chunk4_5_checked, root1Node26Step1Chunk5_0_checked, root1Node26Step1Chunk5_1_checked, root1Node26Step1Chunk5_2_checked, root1Node26Step1Chunk5_3_checked, root1Node26Step1Chunk5_4_checked, root1Node26Step1Chunk5_5_checked, root1Node26Step1Chunk6_0_checked, root1Node26Step1Chunk6_1_checked, root1Node26Step1Chunk6_2_checked, root1Node26Step1Chunk6_3_checked, root1Node26Step1Chunk6_4_checked, root1Node26Step1Chunk6_5_checked, root1Node26Step1Chunk7_0_checked, root1Node26Step1Chunk7_1_checked, root1Node26Step1Chunk7_2_checked, root1Node26Step1Chunk7_3_checked, root1Node26Step1Chunk7_4_checked, root1Node26Step1Chunk7_5_checked, root1Node26Step1Chunk8_0_checked, root1Node26Step1Chunk8_1_checked, root1Node26Step1Chunk8_2_checked, root1Node26Step1Chunk8_3_checked, root1Node26Step1Chunk8_4_checked, root1Node26Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node27Domains0 : Domains 61 State := restrict root1Node26Domains1 50 (5,5)
def root1Node27Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(3,5),(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,2),(2,4)]
  | _ => some [(1,3),(3,3)]
theorem root1Node27Domains0_fast_eq : root1Node27Domains0 = expandDomains root1Node27Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node27Domains0 v = expandDomains root1Node27Domains0Fast v from by decide) v
def root1Node27Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,3)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(1,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(3,5)]
  | 54 => [(0,3)]
  | 55 => [(4,1)]
  | 56 => [(4,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,4)]
  | _ => [(1,3)]
def root1Node27Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(3,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,4)]
  | _ => some [(1,3)]
theorem root1Node27Domains1_fast_eq : root1Node27Domains1 = expandDomains root1Node27Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node27Domains1 v = expandDomains root1Node27Domains1Fast v from by decide) v
theorem root1Node27Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root1Node27Domains0 root1Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node27Domains0 root1Node27Domains1
    root1Node27Domains0Fast root1Node27Domains1Fast
    root1Node27Domains0_fast_eq root1Node27Domains1_fast_eq (by decide)
theorem root1Node27Step1_checked :
    checkReplacement table46 root1Node27Domains0 root1Node27Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node27Step1Chunk0_0_checked, root1Node27Step1Chunk0_1_checked, root1Node27Step1Chunk0_2_checked, root1Node27Step1Chunk0_3_checked, root1Node27Step1Chunk0_4_checked, root1Node27Step1Chunk0_5_checked, root1Node27Step1Chunk1_0_checked, root1Node27Step1Chunk1_1_checked, root1Node27Step1Chunk1_2_checked, root1Node27Step1Chunk1_3_checked, root1Node27Step1Chunk1_4_checked, root1Node27Step1Chunk1_5_checked, root1Node27Step1Chunk2_0_checked, root1Node27Step1Chunk2_1_checked, root1Node27Step1Chunk2_2_checked, root1Node27Step1Chunk2_3_checked, root1Node27Step1Chunk2_4_checked, root1Node27Step1Chunk2_5_checked, root1Node27Step1Chunk3_0_checked, root1Node27Step1Chunk3_1_checked, root1Node27Step1Chunk3_2_checked, root1Node27Step1Chunk3_3_checked, root1Node27Step1Chunk3_4_checked, root1Node27Step1Chunk3_5_checked, root1Node27Step1Chunk4_0_checked, root1Node27Step1Chunk4_1_checked, root1Node27Step1Chunk4_2_checked, root1Node27Step1Chunk4_3_checked, root1Node27Step1Chunk4_4_checked, root1Node27Step1Chunk4_5_checked, root1Node27Step1Chunk5_0_checked, root1Node27Step1Chunk5_1_checked, root1Node27Step1Chunk5_2_checked, root1Node27Step1Chunk5_3_checked, root1Node27Step1Chunk5_4_checked, root1Node27Step1Chunk5_5_checked, root1Node27Step1Chunk6_0_checked, root1Node27Step1Chunk6_1_checked, root1Node27Step1Chunk6_2_checked, root1Node27Step1Chunk6_3_checked, root1Node27Step1Chunk6_4_checked, root1Node27Step1Chunk6_5_checked, root1Node27Step1Chunk7_0_checked, root1Node27Step1Chunk7_1_checked, root1Node27Step1Chunk7_2_checked, root1Node27Step1Chunk7_3_checked, root1Node27Step1Chunk7_4_checked, root1Node27Step1Chunk7_5_checked, root1Node27Step1Chunk8_0_checked, root1Node27Step1Chunk8_1_checked, root1Node27Step1Chunk8_2_checked, root1Node27Step1Chunk8_3_checked, root1Node27Step1Chunk8_4_checked, root1Node27Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node27Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node27Domains1 (.output 11) = true := by decide
def root1Node28Domains0 : Domains 61 State := restrict root1Node26Domains1 50 (8,5)
def root1Node28Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(3,5),(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,2),(2,4)]
  | _ => some [(1,3),(3,3)]
theorem root1Node28Domains0_fast_eq : root1Node28Domains0 = expandDomains root1Node28Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node28Domains0 v = expandDomains root1Node28Domains0Fast v from by decide) v
def root1Node28Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,3)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(1,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(8,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(6,4)]
  | 48 => [(1,2)]
  | 49 => [(7,4)]
  | 50 => [(8,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(7,5)]
  | 54 => [(0,3)]
  | 55 => [(4,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(6,3)]
  | 59 => [(2,2)]
  | _ => [(3,3)]
def root1Node28Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(6,4)]
  | 48 => some [(1,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(7,5)]
  | 54 => some [(0,3)]
  | 55 => some [(4,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(6,3)]
  | 59 => some [(2,2)]
  | _ => some [(3,3)]
theorem root1Node28Domains1_fast_eq : root1Node28Domains1 = expandDomains root1Node28Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node28Domains1 v = expandDomains root1Node28Domains1Fast v from by decide) v
theorem root1Node28Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root1Node28Domains0 root1Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node28Domains0 root1Node28Domains1
    root1Node28Domains0Fast root1Node28Domains1Fast
    root1Node28Domains0_fast_eq root1Node28Domains1_fast_eq (by decide)
theorem root1Node28Step1_checked :
    checkReplacement table46 root1Node28Domains0 root1Node28Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node28Step1Chunk0_0_checked, root1Node28Step1Chunk0_1_checked, root1Node28Step1Chunk0_2_checked, root1Node28Step1Chunk0_3_checked, root1Node28Step1Chunk0_4_checked, root1Node28Step1Chunk0_5_checked, root1Node28Step1Chunk1_0_checked, root1Node28Step1Chunk1_1_checked, root1Node28Step1Chunk1_2_checked, root1Node28Step1Chunk1_3_checked, root1Node28Step1Chunk1_4_checked, root1Node28Step1Chunk1_5_checked, root1Node28Step1Chunk2_0_checked, root1Node28Step1Chunk2_1_checked, root1Node28Step1Chunk2_2_checked, root1Node28Step1Chunk2_3_checked, root1Node28Step1Chunk2_4_checked, root1Node28Step1Chunk2_5_checked, root1Node28Step1Chunk3_0_checked, root1Node28Step1Chunk3_1_checked, root1Node28Step1Chunk3_2_checked, root1Node28Step1Chunk3_3_checked, root1Node28Step1Chunk3_4_checked, root1Node28Step1Chunk3_5_checked, root1Node28Step1Chunk4_0_checked, root1Node28Step1Chunk4_1_checked, root1Node28Step1Chunk4_2_checked, root1Node28Step1Chunk4_3_checked, root1Node28Step1Chunk4_4_checked, root1Node28Step1Chunk4_5_checked, root1Node28Step1Chunk5_0_checked, root1Node28Step1Chunk5_1_checked, root1Node28Step1Chunk5_2_checked, root1Node28Step1Chunk5_3_checked, root1Node28Step1Chunk5_4_checked, root1Node28Step1Chunk5_5_checked, root1Node28Step1Chunk6_0_checked, root1Node28Step1Chunk6_1_checked, root1Node28Step1Chunk6_2_checked, root1Node28Step1Chunk6_3_checked, root1Node28Step1Chunk6_4_checked, root1Node28Step1Chunk6_5_checked, root1Node28Step1Chunk7_0_checked, root1Node28Step1Chunk7_1_checked, root1Node28Step1Chunk7_2_checked, root1Node28Step1Chunk7_3_checked, root1Node28Step1Chunk7_4_checked, root1Node28Step1Chunk7_5_checked, root1Node28Step1Chunk8_0_checked, root1Node28Step1Chunk8_1_checked, root1Node28Step1Chunk8_2_checked, root1Node28Step1Chunk8_3_checked, root1Node28Step1Chunk8_4_checked, root1Node28Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node28Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node28Domains1 (.output 12) = true := by decide
def root1Node29Domains0 : Domains 61 State := restrict root1Node25Domains1 37 (6,3)
def root1Node29Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(8,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,1),(6,4)]
  | 48 => some [(1,2),(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(5,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,2),(2,4),(4,4)]
  | _ => some [(0,0),(1,3),(3,3)]
theorem root1Node29Domains0_fast_eq : root1Node29Domains0 = expandDomains root1Node29Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node29Domains0 v = expandDomains root1Node29Domains0Fast v from by decide) v
def root1Node29Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(3,4)]
  | 1 => [(6,3)]
  | 2 => [(7,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(2,3)]
  | 6 => [(0,2)]
  | 7 => [(1,1)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(0,3)]
  | 34 => [(8,1)]
  | 35 => [(1,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(4,2)]
  | 42 => [(5,3)]
  | 43 => [(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(7,4)]
  | 50 => [(5,2)]
  | 51 => [(8,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(1,0)]
  | 55 => [(2,1)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(0,0)]
def root1Node29Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(3,4)]
  | 1 => some [(6,3)]
  | 2 => some [(7,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(2,3)]
  | 6 => some [(0,2)]
  | 7 => some [(1,1)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3)]
  | 34 => some [(8,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(4,2)]
  | 42 => some [(5,3)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(1,0)]
  | 55 => some [(2,1)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(0,0)]
theorem root1Node29Domains1_fast_eq : root1Node29Domains1 = expandDomains root1Node29Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node29Domains1 v = expandDomains root1Node29Domains1Fast v from by decide) v
theorem root1Node29Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root1Node29Domains0 root1Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node29Domains0 root1Node29Domains1
    root1Node29Domains0Fast root1Node29Domains1Fast
    root1Node29Domains0_fast_eq root1Node29Domains1_fast_eq (by decide)
theorem root1Node29Step1_checked :
    checkReplacement table46 root1Node29Domains0 root1Node29Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node29Step1Chunk0_0_checked, root1Node29Step1Chunk0_1_checked, root1Node29Step1Chunk0_2_checked, root1Node29Step1Chunk0_3_checked, root1Node29Step1Chunk0_4_checked, root1Node29Step1Chunk0_5_checked, root1Node29Step1Chunk1_0_checked, root1Node29Step1Chunk1_1_checked, root1Node29Step1Chunk1_2_checked, root1Node29Step1Chunk1_3_checked, root1Node29Step1Chunk1_4_checked, root1Node29Step1Chunk1_5_checked, root1Node29Step1Chunk2_0_checked, root1Node29Step1Chunk2_1_checked, root1Node29Step1Chunk2_2_checked, root1Node29Step1Chunk2_3_checked, root1Node29Step1Chunk2_4_checked, root1Node29Step1Chunk2_5_checked, root1Node29Step1Chunk3_0_checked, root1Node29Step1Chunk3_1_checked, root1Node29Step1Chunk3_2_checked, root1Node29Step1Chunk3_3_checked, root1Node29Step1Chunk3_4_checked, root1Node29Step1Chunk3_5_checked, root1Node29Step1Chunk4_0_checked, root1Node29Step1Chunk4_1_checked, root1Node29Step1Chunk4_2_checked, root1Node29Step1Chunk4_3_checked, root1Node29Step1Chunk4_4_checked, root1Node29Step1Chunk4_5_checked, root1Node29Step1Chunk5_0_checked, root1Node29Step1Chunk5_1_checked, root1Node29Step1Chunk5_2_checked, root1Node29Step1Chunk5_3_checked, root1Node29Step1Chunk5_4_checked, root1Node29Step1Chunk5_5_checked, root1Node29Step1Chunk6_0_checked, root1Node29Step1Chunk6_1_checked, root1Node29Step1Chunk6_2_checked, root1Node29Step1Chunk6_3_checked, root1Node29Step1Chunk6_4_checked, root1Node29Step1Chunk6_5_checked, root1Node29Step1Chunk7_0_checked, root1Node29Step1Chunk7_1_checked, root1Node29Step1Chunk7_2_checked, root1Node29Step1Chunk7_3_checked, root1Node29Step1Chunk7_4_checked, root1Node29Step1Chunk7_5_checked, root1Node29Step1Chunk8_0_checked, root1Node29Step1Chunk8_1_checked, root1Node29Step1Chunk8_2_checked, root1Node29Step1Chunk8_3_checked, root1Node29Step1Chunk8_4_checked, root1Node29Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
