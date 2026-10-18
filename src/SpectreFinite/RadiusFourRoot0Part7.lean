module

public import SpectreFinite.RadiusFourRoot0Part6
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable0
public import SpectreFinite.RadiusFourTable3
public import SpectreFinite.RadiusFourTable7

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node14Domains0 : Domains 61 State := restrict root0Node13Domains4 0 (4,0)
def root0Node14Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3),(8,3)]
  | 2 => some [(5,2),(5,5),(8,2)]
  | 3 => some [(1,0),(3,0),(5,0)]
  | 4 => some [(2,1),(2,5),(4,5)]
  | 5 => some [(5,1),(5,4)]
  | 6 => some [(0,1),(1,4)]
  | 7 => some [(0,5),(6,2)]
  | 8 => some [(4,4),(8,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2),(7,2)]
  | 11 => some [(4,3),(5,3),(8,3)]
  | 12 => some [(7,5),(8,5)]
  | 13 => some [(1,0),(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1),(8,1)]
  | 18 => some [(7,4)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(8,1)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(1,1)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(7,1)]
theorem root0Node14Domains0_fast_eq : root0Node14Domains0 = expandDomains root0Node14Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node14Domains0 v = expandDomains root0Node14Domains0Fast v from by decide) v
def root0Node14Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2),(8,2)]
  | 3 => [(5,0)]
  | 4 => [(4,5)]
  | 5 => [(5,1)]
  | 6 => [(0,1)]
  | 7 => [(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(5,3),(8,3)]
  | 12 => [(8,5)]
  | 13 => [(1,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1),(8,1)]
  | 18 => [(7,4)]
  | 19 => [(1,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(8,5)]
  | 26 => [(8,1)]
  | 27 => [(6,5)]
  | 28 => [(0,4)]
  | 29 => [(5,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(6,3)]
  | 34 => [(7,2)]
  | 35 => [(5,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(4,1)]
  | 41 => [(0,2)]
  | 42 => [(1,1)]
  | 43 => [(4,4)]
  | 44 => [(1,4)]
  | 45 => [(0,5)]
  | 46 => [(2,0)]
  | 47 => [(7,3)]
  | 48 => [(5,2)]
  | 49 => [(8,0)]
  | 50 => [(7,5)]
  | 51 => [(6,0)]
  | 52 => [(3,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(8,2)]
  | 57 => [(5,0)]
  | 58 => [(4,5)]
  | 59 => [(1,0)]
  | _ => [(7,1)]
def root0Node14Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2),(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(5,1)]
  | 6 => some [(0,1)]
  | 7 => some [(6,2)]
  | 8 => some [(8,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(5,3),(8,3)]
  | 12 => some [(8,5)]
  | 13 => some [(1,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1),(8,1)]
  | 18 => some [(7,4)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(8,1)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(1,1)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(7,1)]
theorem root0Node14Domains1_fast_eq : root0Node14Domains1 = expandDomains root0Node14Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node14Domains1 v = expandDomains root0Node14Domains1Fast v from by decide) v
theorem root0Node14Step1Chunk0_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk0_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk0_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk0_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk0_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk0_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows0_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk1_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows1_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk2_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows2_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk3_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows3_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk4_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows4_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk5_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows5_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk6_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows6_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk7_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows7_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_0_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_0⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_1_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_1⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_2_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_2⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_3_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_3⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_4_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_4⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1Chunk8_5_checked :
    checkNarrowing ⟨table7Scope, table7Rows8_5⟩
      root0Node14Domains0 root0Node14Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node14Domains0 root0Node14Domains1
    root0Node14Domains0Fast root0Node14Domains1Fast
    root0Node14Domains0_fast_eq root0Node14Domains1_fast_eq (by decide)
theorem root0Node14Step1_checked :
    checkReplacement table7 root0Node14Domains0 root0Node14Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node14Step1Chunk0_0_checked, root0Node14Step1Chunk0_1_checked, root0Node14Step1Chunk0_2_checked, root0Node14Step1Chunk0_3_checked, root0Node14Step1Chunk0_4_checked, root0Node14Step1Chunk0_5_checked, root0Node14Step1Chunk1_0_checked, root0Node14Step1Chunk1_1_checked, root0Node14Step1Chunk1_2_checked, root0Node14Step1Chunk1_3_checked, root0Node14Step1Chunk1_4_checked, root0Node14Step1Chunk1_5_checked, root0Node14Step1Chunk2_0_checked, root0Node14Step1Chunk2_1_checked, root0Node14Step1Chunk2_2_checked, root0Node14Step1Chunk2_3_checked, root0Node14Step1Chunk2_4_checked, root0Node14Step1Chunk2_5_checked, root0Node14Step1Chunk3_0_checked, root0Node14Step1Chunk3_1_checked, root0Node14Step1Chunk3_2_checked, root0Node14Step1Chunk3_3_checked, root0Node14Step1Chunk3_4_checked, root0Node14Step1Chunk3_5_checked, root0Node14Step1Chunk4_0_checked, root0Node14Step1Chunk4_1_checked, root0Node14Step1Chunk4_2_checked, root0Node14Step1Chunk4_3_checked, root0Node14Step1Chunk4_4_checked, root0Node14Step1Chunk4_5_checked, root0Node14Step1Chunk5_0_checked, root0Node14Step1Chunk5_1_checked, root0Node14Step1Chunk5_2_checked, root0Node14Step1Chunk5_3_checked, root0Node14Step1Chunk5_4_checked, root0Node14Step1Chunk5_5_checked, root0Node14Step1Chunk6_0_checked, root0Node14Step1Chunk6_1_checked, root0Node14Step1Chunk6_2_checked, root0Node14Step1Chunk6_3_checked, root0Node14Step1Chunk6_4_checked, root0Node14Step1Chunk6_5_checked, root0Node14Step1Chunk7_0_checked, root0Node14Step1Chunk7_1_checked, root0Node14Step1Chunk7_2_checked, root0Node14Step1Chunk7_3_checked, root0Node14Step1Chunk7_4_checked, root0Node14Step1Chunk7_5_checked, root0Node14Step1Chunk8_0_checked, root0Node14Step1Chunk8_1_checked, root0Node14Step1Chunk8_2_checked, root0Node14Step1Chunk8_3_checked, root0Node14Step1Chunk8_4_checked, root0Node14Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node15Domains0 : Domains 61 State := restrict root0Node14Domains1 2 (5,2)
def root0Node15Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(5,1)]
  | 6 => some [(0,1)]
  | 7 => some [(6,2)]
  | 8 => some [(8,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(5,3),(8,3)]
  | 12 => some [(8,5)]
  | 13 => some [(1,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1),(8,1)]
  | 18 => some [(7,4)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(8,1)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(1,1)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(7,1)]
theorem root0Node15Domains0_fast_eq : root0Node15Domains0 = expandDomains root0Node15Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node15Domains0 v = expandDomains root0Node15Domains0Fast v from by decide) v
def root0Node15Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(5,0)]
  | 4 => [(4,5)]
  | 5 => [(5,1)]
  | 6 => [(0,1)]
  | 7 => [(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(5,3),(8,3)]
  | 12 => [(8,5)]
  | 13 => [(1,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1)]
  | 18 => [(7,4)]
  | 19 => [(1,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(8,5)]
  | 26 => [(8,1)]
  | 27 => [(6,5)]
  | 28 => [(0,4)]
  | 29 => [(5,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(6,3)]
  | 34 => [(7,2)]
  | 35 => [(5,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(4,1)]
  | 41 => [(0,2)]
  | 42 => [(1,1)]
  | 43 => [(4,4)]
  | 44 => [(1,4)]
  | 45 => [(0,5)]
  | 46 => [(2,0)]
  | 47 => [(7,3)]
  | 48 => [(5,2)]
  | 49 => [(8,0)]
  | 50 => [(7,5)]
  | 51 => [(6,0)]
  | 52 => [(3,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(8,2)]
  | 57 => [(5,0)]
  | 58 => [(4,5)]
  | 59 => [(1,0)]
  | _ => [(7,1)]
def root0Node15Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(5,1)]
  | 6 => some [(0,1)]
  | 7 => some [(6,2)]
  | 8 => some [(8,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(5,3),(8,3)]
  | 12 => some [(8,5)]
  | 13 => some [(1,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(7,4)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(8,1)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(1,1)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(7,1)]
theorem root0Node15Domains1_fast_eq : root0Node15Domains1 = expandDomains root0Node15Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node15Domains1 v = expandDomains root0Node15Domains1Fast v from by decide) v
theorem root0Node15Step1Chunk0_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk0_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk0_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk0_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk0_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk0_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk1_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk2_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk3_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk4_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk5_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk6_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk7_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_0⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_1⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_2⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_3⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_4⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1Chunk8_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_5⟩
      root0Node15Domains0 root0Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node15Domains0 root0Node15Domains1
    root0Node15Domains0Fast root0Node15Domains1Fast
    root0Node15Domains0_fast_eq root0Node15Domains1_fast_eq (by decide)
theorem root0Node15Step1_checked :
    checkReplacement table3 root0Node15Domains0 root0Node15Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node15Step1Chunk0_0_checked, root0Node15Step1Chunk0_1_checked, root0Node15Step1Chunk0_2_checked, root0Node15Step1Chunk0_3_checked, root0Node15Step1Chunk0_4_checked, root0Node15Step1Chunk0_5_checked, root0Node15Step1Chunk1_0_checked, root0Node15Step1Chunk1_1_checked, root0Node15Step1Chunk1_2_checked, root0Node15Step1Chunk1_3_checked, root0Node15Step1Chunk1_4_checked, root0Node15Step1Chunk1_5_checked, root0Node15Step1Chunk2_0_checked, root0Node15Step1Chunk2_1_checked, root0Node15Step1Chunk2_2_checked, root0Node15Step1Chunk2_3_checked, root0Node15Step1Chunk2_4_checked, root0Node15Step1Chunk2_5_checked, root0Node15Step1Chunk3_0_checked, root0Node15Step1Chunk3_1_checked, root0Node15Step1Chunk3_2_checked, root0Node15Step1Chunk3_3_checked, root0Node15Step1Chunk3_4_checked, root0Node15Step1Chunk3_5_checked, root0Node15Step1Chunk4_0_checked, root0Node15Step1Chunk4_1_checked, root0Node15Step1Chunk4_2_checked, root0Node15Step1Chunk4_3_checked, root0Node15Step1Chunk4_4_checked, root0Node15Step1Chunk4_5_checked, root0Node15Step1Chunk5_0_checked, root0Node15Step1Chunk5_1_checked, root0Node15Step1Chunk5_2_checked, root0Node15Step1Chunk5_3_checked, root0Node15Step1Chunk5_4_checked, root0Node15Step1Chunk5_5_checked, root0Node15Step1Chunk6_0_checked, root0Node15Step1Chunk6_1_checked, root0Node15Step1Chunk6_2_checked, root0Node15Step1Chunk6_3_checked, root0Node15Step1Chunk6_4_checked, root0Node15Step1Chunk6_5_checked, root0Node15Step1Chunk7_0_checked, root0Node15Step1Chunk7_1_checked, root0Node15Step1Chunk7_2_checked, root0Node15Step1Chunk7_3_checked, root0Node15Step1Chunk7_4_checked, root0Node15Step1Chunk7_5_checked, root0Node15Step1Chunk8_0_checked, root0Node15Step1Chunk8_1_checked, root0Node15Step1Chunk8_2_checked, root0Node15Step1Chunk8_3_checked, root0Node15Step1Chunk8_4_checked, root0Node15Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node16Domains0 : Domains 61 State := restrict root0Node15Domains1 11 (5,3)
def root0Node16Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(5,1)]
  | 6 => some [(0,1)]
  | 7 => some [(6,2)]
  | 8 => some [(8,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(5,3)]
  | 12 => some [(8,5)]
  | 13 => some [(1,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(7,4)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(8,1)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(1,1)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(7,1)]
theorem root0Node16Domains0_fast_eq : root0Node16Domains0 = expandDomains root0Node16Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node16Domains0 v = expandDomains root0Node16Domains0Fast v from by decide) v
theorem root0Node16Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node16Domains0 (.output 6) = true := by decide
def root0Node17Domains0 : Domains 61 State := restrict root0Node15Domains1 11 (8,3)
def root0Node17Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(5,1)]
  | 6 => some [(0,1)]
  | 7 => some [(6,2)]
  | 8 => some [(8,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(8,3)]
  | 12 => some [(8,5)]
  | 13 => some [(1,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1)]
  | 18 => some [(7,4)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(8,1)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(1,1)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(7,1)]
theorem root0Node17Domains0_fast_eq : root0Node17Domains0 = expandDomains root0Node17Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node17Domains0 v = expandDomains root0Node17Domains0Fast v from by decide) v
theorem root0Node17Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node17Domains0 (.output 7) = true := by decide
def root0Node18Domains0 : Domains 61 State := restrict root0Node14Domains1 2 (8,2)
def root0Node18Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(5,1)]
  | 6 => some [(0,1)]
  | 7 => some [(6,2)]
  | 8 => some [(8,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(5,3),(8,3)]
  | 12 => some [(8,5)]
  | 13 => some [(1,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1),(8,1)]
  | 18 => some [(7,4)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(8,1)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(1,1)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(7,1)]
theorem root0Node18Domains0_fast_eq : root0Node18Domains0 = expandDomains root0Node18Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node18Domains0 v = expandDomains root0Node18Domains0Fast v from by decide) v
def root0Node18Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(8,2)]
  | 3 => [(5,0)]
  | 4 => [(4,5)]
  | 5 => [(5,1)]
  | 6 => [(0,1)]
  | 7 => [(6,2)]
  | 8 => [(8,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(8,3)]
  | 12 => [(8,5)]
  | 13 => [(1,0)]
  | 14 => [(7,1)]
  | 15 => [(1,5)]
  | 16 => [(6,1)]
  | 17 => [(5,1),(8,1)]
  | 18 => [(7,4)]
  | 19 => [(1,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(8,3)]
  | 25 => [(8,5)]
  | 26 => [(8,1)]
  | 27 => [(6,5)]
  | 28 => [(0,4)]
  | 29 => [(5,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(6,3)]
  | 34 => [(7,2)]
  | 35 => [(5,5)]
  | 36 => [(7,0)]
  | 37 => [(4,3)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(4,1)]
  | 41 => [(0,2)]
  | 42 => [(1,1)]
  | 43 => [(4,4)]
  | 44 => [(1,4)]
  | 45 => [(0,5)]
  | 46 => [(2,0)]
  | 47 => [(7,3)]
  | 48 => [(5,2)]
  | 49 => [(8,0)]
  | 50 => [(7,5)]
  | 51 => [(6,0)]
  | 52 => [(3,1)]
  | 53 => [(0,1)]
  | 54 => [(6,2)]
  | 55 => [(8,4)]
  | 56 => [(8,2)]
  | 57 => [(5,0)]
  | 58 => [(4,5)]
  | 59 => [(1,0)]
  | _ => [(7,1)]
def root0Node18Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(8,2)]
  | 3 => some [(5,0)]
  | 4 => some [(4,5)]
  | 5 => some [(5,1)]
  | 6 => some [(0,1)]
  | 7 => some [(6,2)]
  | 8 => some [(8,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(8,3)]
  | 12 => some [(8,5)]
  | 13 => some [(1,0)]
  | 14 => some [(7,1)]
  | 15 => some [(1,5)]
  | 16 => some [(6,1)]
  | 17 => some [(5,1),(8,1)]
  | 18 => some [(7,4)]
  | 19 => some [(1,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(8,3)]
  | 25 => some [(8,5)]
  | 26 => some [(8,1)]
  | 27 => some [(6,5)]
  | 28 => some [(0,4)]
  | 29 => some [(5,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(5,5)]
  | 36 => some [(7,0)]
  | 37 => some [(4,3)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(4,1)]
  | 41 => some [(0,2)]
  | 42 => some [(1,1)]
  | 43 => some [(4,4)]
  | 44 => some [(1,4)]
  | 45 => some [(0,5)]
  | 46 => some [(2,0)]
  | 47 => some [(7,3)]
  | 48 => some [(5,2)]
  | 49 => some [(8,0)]
  | 50 => some [(7,5)]
  | 51 => some [(6,0)]
  | 52 => some [(3,1)]
  | 53 => some [(0,1)]
  | 54 => some [(6,2)]
  | 55 => some [(8,4)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(1,0)]
  | _ => some [(7,1)]
theorem root0Node18Domains1_fast_eq : root0Node18Domains1 = expandDomains root0Node18Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node18Domains1 v = expandDomains root0Node18Domains1Fast v from by decide) v
theorem root0Node18Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root0Node18Domains0 root0Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node18Domains0 root0Node18Domains1
    root0Node18Domains0Fast root0Node18Domains1Fast
    root0Node18Domains0_fast_eq root0Node18Domains1_fast_eq (by decide)
theorem root0Node18Step1_checked :
    checkReplacement table0 root0Node18Domains0 root0Node18Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node18Step1Chunk0_0_checked, root0Node18Step1Chunk0_1_checked, root0Node18Step1Chunk0_2_checked, root0Node18Step1Chunk0_3_checked, root0Node18Step1Chunk0_4_checked, root0Node18Step1Chunk0_5_checked, root0Node18Step1Chunk1_0_checked, root0Node18Step1Chunk1_1_checked, root0Node18Step1Chunk1_2_checked, root0Node18Step1Chunk1_3_checked, root0Node18Step1Chunk1_4_checked, root0Node18Step1Chunk1_5_checked, root0Node18Step1Chunk2_0_checked, root0Node18Step1Chunk2_1_checked, root0Node18Step1Chunk2_2_checked, root0Node18Step1Chunk2_3_checked, root0Node18Step1Chunk2_4_checked, root0Node18Step1Chunk2_5_checked, root0Node18Step1Chunk3_0_checked, root0Node18Step1Chunk3_1_checked, root0Node18Step1Chunk3_2_checked, root0Node18Step1Chunk3_3_checked, root0Node18Step1Chunk3_4_checked, root0Node18Step1Chunk3_5_checked, root0Node18Step1Chunk4_0_checked, root0Node18Step1Chunk4_1_checked, root0Node18Step1Chunk4_2_checked, root0Node18Step1Chunk4_3_checked, root0Node18Step1Chunk4_4_checked, root0Node18Step1Chunk4_5_checked, root0Node18Step1Chunk5_0_checked, root0Node18Step1Chunk5_1_checked, root0Node18Step1Chunk5_2_checked, root0Node18Step1Chunk5_3_checked, root0Node18Step1Chunk5_4_checked, root0Node18Step1Chunk5_5_checked, root0Node18Step1Chunk6_0_checked, root0Node18Step1Chunk6_1_checked, root0Node18Step1Chunk6_2_checked, root0Node18Step1Chunk6_3_checked, root0Node18Step1Chunk6_4_checked, root0Node18Step1Chunk6_5_checked, root0Node18Step1Chunk7_0_checked, root0Node18Step1Chunk7_1_checked, root0Node18Step1Chunk7_2_checked, root0Node18Step1Chunk7_3_checked, root0Node18Step1Chunk7_4_checked, root0Node18Step1Chunk7_5_checked, root0Node18Step1Chunk8_0_checked, root0Node18Step1Chunk8_1_checked, root0Node18Step1Chunk8_2_checked, root0Node18Step1Chunk8_3_checked, root0Node18Step1Chunk8_4_checked, root0Node18Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
