module

public import SpectreFinite.RadiusFourRoot7Part37
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable19
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable35

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node113Domains0 : Domains 61 State := restrict root7Node111Domains1 35 (8,4)
def root7Node113Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(4,1)]
  | 35 => some [(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(2,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(3,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node113Domains0_fast_eq : root7Node113Domains0 = expandDomains root7Node113Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node113Domains0 v = expandDomains root7Node113Domains0Fast v from by decide) v
def root7Node113Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(4,1)]
  | 35 => [(8,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(2,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(3,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(8,4)]
  | 57 => [(6,4)]
  | 58 => [(1,2)]
  | 59 => [(8,4)]
  | _ => [(0,0)]
def root7Node113Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(4,1)]
  | 35 => some [(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(2,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(3,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(8,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node113Domains1_fast_eq : root7Node113Domains1 = expandDomains root7Node113Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node113Domains1 v = expandDomains root7Node113Domains1Fast v from by decide) v
theorem root7Node113Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root7Node113Domains0 root7Node113Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node113Domains0 root7Node113Domains1
    root7Node113Domains0Fast root7Node113Domains1Fast
    root7Node113Domains0_fast_eq root7Node113Domains1_fast_eq (by decide)
theorem root7Node113Step1_checked :
    checkReplacement table35 root7Node113Domains0 root7Node113Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node113Step1Chunk0_0_checked, root7Node113Step1Chunk0_1_checked, root7Node113Step1Chunk0_2_checked, root7Node113Step1Chunk0_3_checked, root7Node113Step1Chunk0_4_checked, root7Node113Step1Chunk0_5_checked, root7Node113Step1Chunk1_0_checked, root7Node113Step1Chunk1_1_checked, root7Node113Step1Chunk1_2_checked, root7Node113Step1Chunk1_3_checked, root7Node113Step1Chunk1_4_checked, root7Node113Step1Chunk1_5_checked, root7Node113Step1Chunk2_0_checked, root7Node113Step1Chunk2_1_checked, root7Node113Step1Chunk2_2_checked, root7Node113Step1Chunk2_3_checked, root7Node113Step1Chunk2_4_checked, root7Node113Step1Chunk2_5_checked, root7Node113Step1Chunk3_0_checked, root7Node113Step1Chunk3_1_checked, root7Node113Step1Chunk3_2_checked, root7Node113Step1Chunk3_3_checked, root7Node113Step1Chunk3_4_checked, root7Node113Step1Chunk3_5_checked, root7Node113Step1Chunk4_0_checked, root7Node113Step1Chunk4_1_checked, root7Node113Step1Chunk4_2_checked, root7Node113Step1Chunk4_3_checked, root7Node113Step1Chunk4_4_checked, root7Node113Step1Chunk4_5_checked, root7Node113Step1Chunk5_0_checked, root7Node113Step1Chunk5_1_checked, root7Node113Step1Chunk5_2_checked, root7Node113Step1Chunk5_3_checked, root7Node113Step1Chunk5_4_checked, root7Node113Step1Chunk5_5_checked, root7Node113Step1Chunk6_0_checked, root7Node113Step1Chunk6_1_checked, root7Node113Step1Chunk6_2_checked, root7Node113Step1Chunk6_3_checked, root7Node113Step1Chunk6_4_checked, root7Node113Step1Chunk6_5_checked, root7Node113Step1Chunk7_0_checked, root7Node113Step1Chunk7_1_checked, root7Node113Step1Chunk7_2_checked, root7Node113Step1Chunk7_3_checked, root7Node113Step1Chunk7_4_checked, root7Node113Step1Chunk7_5_checked, root7Node113Step1Chunk8_0_checked, root7Node113Step1Chunk8_1_checked, root7Node113Step1Chunk8_2_checked, root7Node113Step1Chunk8_3_checked, root7Node113Step1Chunk8_4_checked, root7Node113Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node113Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node113Domains1 (.output 55) = true := by decide
def root7Node114Domains0 : Domains 61 State := restrict root7Node110Domains3 16 (8,0)
def root7Node114Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5),(3,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(4,1)]
  | 35 => some [(5,4),(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(2,0),(2,4)]
  | 42 => some [(1,3),(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(3,1),(7,1)]
  | 49 => some [(0,1),(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node114Domains0_fast_eq : root7Node114Domains0 = expandDomains root7Node114Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node114Domains0 v = expandDomains root7Node114Domains0Fast v from by decide) v
def root7Node114Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(3,5)]
  | 33 => [(0,3)]
  | 34 => [(4,1)]
  | 35 => [(5,4),(8,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(2,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(6,5)]
  | 50 => [(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(6,4)]
  | 58 => [(1,2)]
  | 59 => [(8,4)]
  | _ => [(0,0)]
def root7Node114Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(3,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1)]
  | 35 => some [(5,4),(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(2,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node114Domains1_fast_eq : root7Node114Domains1 = expandDomains root7Node114Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node114Domains1 v = expandDomains root7Node114Domains1Fast v from by decide) v
theorem root7Node114Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root7Node114Domains0 root7Node114Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node114Domains0 root7Node114Domains1
    root7Node114Domains0Fast root7Node114Domains1Fast
    root7Node114Domains0_fast_eq root7Node114Domains1_fast_eq (by decide)
theorem root7Node114Step1_checked :
    checkReplacement table23 root7Node114Domains0 root7Node114Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node114Step1Chunk0_0_checked, root7Node114Step1Chunk0_1_checked, root7Node114Step1Chunk0_2_checked, root7Node114Step1Chunk0_3_checked, root7Node114Step1Chunk0_4_checked, root7Node114Step1Chunk0_5_checked, root7Node114Step1Chunk1_0_checked, root7Node114Step1Chunk1_1_checked, root7Node114Step1Chunk1_2_checked, root7Node114Step1Chunk1_3_checked, root7Node114Step1Chunk1_4_checked, root7Node114Step1Chunk1_5_checked, root7Node114Step1Chunk2_0_checked, root7Node114Step1Chunk2_1_checked, root7Node114Step1Chunk2_2_checked, root7Node114Step1Chunk2_3_checked, root7Node114Step1Chunk2_4_checked, root7Node114Step1Chunk2_5_checked, root7Node114Step1Chunk3_0_checked, root7Node114Step1Chunk3_1_checked, root7Node114Step1Chunk3_2_checked, root7Node114Step1Chunk3_3_checked, root7Node114Step1Chunk3_4_checked, root7Node114Step1Chunk3_5_checked, root7Node114Step1Chunk4_0_checked, root7Node114Step1Chunk4_1_checked, root7Node114Step1Chunk4_2_checked, root7Node114Step1Chunk4_3_checked, root7Node114Step1Chunk4_4_checked, root7Node114Step1Chunk4_5_checked, root7Node114Step1Chunk5_0_checked, root7Node114Step1Chunk5_1_checked, root7Node114Step1Chunk5_2_checked, root7Node114Step1Chunk5_3_checked, root7Node114Step1Chunk5_4_checked, root7Node114Step1Chunk5_5_checked, root7Node114Step1Chunk6_0_checked, root7Node114Step1Chunk6_1_checked, root7Node114Step1Chunk6_2_checked, root7Node114Step1Chunk6_3_checked, root7Node114Step1Chunk6_4_checked, root7Node114Step1Chunk6_5_checked, root7Node114Step1Chunk7_0_checked, root7Node114Step1Chunk7_1_checked, root7Node114Step1Chunk7_2_checked, root7Node114Step1Chunk7_3_checked, root7Node114Step1Chunk7_4_checked, root7Node114Step1Chunk7_5_checked, root7Node114Step1Chunk8_0_checked, root7Node114Step1Chunk8_1_checked, root7Node114Step1Chunk8_2_checked, root7Node114Step1Chunk8_3_checked, root7Node114Step1Chunk8_4_checked, root7Node114Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node115Domains0 : Domains 61 State := restrict root7Node114Domains1 35 (5,4)
def root7Node115Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(3,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1)]
  | 35 => some [(5,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(2,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node115Domains0_fast_eq : root7Node115Domains0 = expandDomains root7Node115Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node115Domains0 v = expandDomains root7Node115Domains0Fast v from by decide) v
def root7Node115Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(3,5)]
  | 33 => [(0,3)]
  | 34 => [(4,1)]
  | 35 => [(5,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(2,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(6,5)]
  | 50 => [(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(5,4)]
  | 57 => [(6,4)]
  | 58 => [(1,2)]
  | 59 => [(8,4)]
  | _ => [(0,0)]
def root7Node115Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(3,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1)]
  | 35 => some [(5,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(2,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node115Domains1_fast_eq : root7Node115Domains1 = expandDomains root7Node115Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node115Domains1 v = expandDomains root7Node115Domains1Fast v from by decide) v
theorem root7Node115Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root7Node115Domains0 root7Node115Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node115Domains0 root7Node115Domains1
    root7Node115Domains0Fast root7Node115Domains1Fast
    root7Node115Domains0_fast_eq root7Node115Domains1_fast_eq (by decide)
theorem root7Node115Step1_checked :
    checkReplacement table35 root7Node115Domains0 root7Node115Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node115Step1Chunk0_0_checked, root7Node115Step1Chunk0_1_checked, root7Node115Step1Chunk0_2_checked, root7Node115Step1Chunk0_3_checked, root7Node115Step1Chunk0_4_checked, root7Node115Step1Chunk0_5_checked, root7Node115Step1Chunk1_0_checked, root7Node115Step1Chunk1_1_checked, root7Node115Step1Chunk1_2_checked, root7Node115Step1Chunk1_3_checked, root7Node115Step1Chunk1_4_checked, root7Node115Step1Chunk1_5_checked, root7Node115Step1Chunk2_0_checked, root7Node115Step1Chunk2_1_checked, root7Node115Step1Chunk2_2_checked, root7Node115Step1Chunk2_3_checked, root7Node115Step1Chunk2_4_checked, root7Node115Step1Chunk2_5_checked, root7Node115Step1Chunk3_0_checked, root7Node115Step1Chunk3_1_checked, root7Node115Step1Chunk3_2_checked, root7Node115Step1Chunk3_3_checked, root7Node115Step1Chunk3_4_checked, root7Node115Step1Chunk3_5_checked, root7Node115Step1Chunk4_0_checked, root7Node115Step1Chunk4_1_checked, root7Node115Step1Chunk4_2_checked, root7Node115Step1Chunk4_3_checked, root7Node115Step1Chunk4_4_checked, root7Node115Step1Chunk4_5_checked, root7Node115Step1Chunk5_0_checked, root7Node115Step1Chunk5_1_checked, root7Node115Step1Chunk5_2_checked, root7Node115Step1Chunk5_3_checked, root7Node115Step1Chunk5_4_checked, root7Node115Step1Chunk5_5_checked, root7Node115Step1Chunk6_0_checked, root7Node115Step1Chunk6_1_checked, root7Node115Step1Chunk6_2_checked, root7Node115Step1Chunk6_3_checked, root7Node115Step1Chunk6_4_checked, root7Node115Step1Chunk6_5_checked, root7Node115Step1Chunk7_0_checked, root7Node115Step1Chunk7_1_checked, root7Node115Step1Chunk7_2_checked, root7Node115Step1Chunk7_3_checked, root7Node115Step1Chunk7_4_checked, root7Node115Step1Chunk7_5_checked, root7Node115Step1Chunk8_0_checked, root7Node115Step1Chunk8_1_checked, root7Node115Step1Chunk8_2_checked, root7Node115Step1Chunk8_3_checked, root7Node115Step1Chunk8_4_checked, root7Node115Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node115Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node115Domains1 (.output 56) = true := by decide
def root7Node116Domains0 : Domains 61 State := restrict root7Node114Domains1 35 (8,4)
def root7Node116Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(3,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1)]
  | 35 => some [(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(2,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node116Domains0_fast_eq : root7Node116Domains0 = expandDomains root7Node116Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node116Domains0 v = expandDomains root7Node116Domains0Fast v from by decide) v
def root7Node116Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(8,0)]
  | 17 => [(7,3)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(6,4)]
  | 25 => [(1,2)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(3,5)]
  | 33 => [(0,3)]
  | 34 => [(4,1)]
  | 35 => [(8,4)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(2,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(7,1)]
  | 49 => [(6,5)]
  | 50 => [(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(8,4)]
  | 57 => [(6,4)]
  | 58 => [(1,2)]
  | 59 => [(8,4)]
  | _ => [(0,0)]
def root7Node116Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(8,0)]
  | 17 => some [(7,3)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(6,4)]
  | 25 => some [(1,2)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(3,5)]
  | 33 => some [(0,3)]
  | 34 => some [(4,1)]
  | 35 => some [(8,4)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(2,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(7,1)]
  | 49 => some [(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(8,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node116Domains1_fast_eq : root7Node116Domains1 = expandDomains root7Node116Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node116Domains1 v = expandDomains root7Node116Domains1Fast v from by decide) v
theorem root7Node116Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root7Node116Domains0 root7Node116Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node116Domains0 root7Node116Domains1
    root7Node116Domains0Fast root7Node116Domains1Fast
    root7Node116Domains0_fast_eq root7Node116Domains1_fast_eq (by decide)
theorem root7Node116Step1_checked :
    checkReplacement table35 root7Node116Domains0 root7Node116Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node116Step1Chunk0_0_checked, root7Node116Step1Chunk0_1_checked, root7Node116Step1Chunk0_2_checked, root7Node116Step1Chunk0_3_checked, root7Node116Step1Chunk0_4_checked, root7Node116Step1Chunk0_5_checked, root7Node116Step1Chunk1_0_checked, root7Node116Step1Chunk1_1_checked, root7Node116Step1Chunk1_2_checked, root7Node116Step1Chunk1_3_checked, root7Node116Step1Chunk1_4_checked, root7Node116Step1Chunk1_5_checked, root7Node116Step1Chunk2_0_checked, root7Node116Step1Chunk2_1_checked, root7Node116Step1Chunk2_2_checked, root7Node116Step1Chunk2_3_checked, root7Node116Step1Chunk2_4_checked, root7Node116Step1Chunk2_5_checked, root7Node116Step1Chunk3_0_checked, root7Node116Step1Chunk3_1_checked, root7Node116Step1Chunk3_2_checked, root7Node116Step1Chunk3_3_checked, root7Node116Step1Chunk3_4_checked, root7Node116Step1Chunk3_5_checked, root7Node116Step1Chunk4_0_checked, root7Node116Step1Chunk4_1_checked, root7Node116Step1Chunk4_2_checked, root7Node116Step1Chunk4_3_checked, root7Node116Step1Chunk4_4_checked, root7Node116Step1Chunk4_5_checked, root7Node116Step1Chunk5_0_checked, root7Node116Step1Chunk5_1_checked, root7Node116Step1Chunk5_2_checked, root7Node116Step1Chunk5_3_checked, root7Node116Step1Chunk5_4_checked, root7Node116Step1Chunk5_5_checked, root7Node116Step1Chunk6_0_checked, root7Node116Step1Chunk6_1_checked, root7Node116Step1Chunk6_2_checked, root7Node116Step1Chunk6_3_checked, root7Node116Step1Chunk6_4_checked, root7Node116Step1Chunk6_5_checked, root7Node116Step1Chunk7_0_checked, root7Node116Step1Chunk7_1_checked, root7Node116Step1Chunk7_2_checked, root7Node116Step1Chunk7_3_checked, root7Node116Step1Chunk7_4_checked, root7Node116Step1Chunk7_5_checked, root7Node116Step1Chunk8_0_checked, root7Node116Step1Chunk8_1_checked, root7Node116Step1Chunk8_2_checked, root7Node116Step1Chunk8_3_checked, root7Node116Step1Chunk8_4_checked, root7Node116Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node116Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node116Domains1 (.output 57) = true := by decide
def root7Node117Domains0 : Domains 61 State := restrict root7Node93Domains3 0 (7,5)
def root7Node117Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3),(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5),(7,3),(8,5)]
  | 6 => some [(4,2),(7,0)]
  | 7 => some [(5,3),(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0),(6,3),(6,4)]
  | 12 => some [(1,2),(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(0,2),(1,5),(7,5)]
  | 19 => some [(0,3),(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => some [(4,2),(7,0),(8,0)]
  | 28 => some [(5,3),(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => some [(1,4),(3,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node117Domains0_fast_eq : root7Node117Domains0 = expandDomains root7Node117Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node117Domains0 v = expandDomains root7Node117Domains0Fast v from by decide) v
def root7Node117Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(0,0),(6,4)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(1,3),(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(1,5),(3,5),(7,5)]
  | 33 => [(0,3),(6,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(0,4),(1,2),(6,2)]
  | 36 => [(1,4),(3,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,2)]
  | 42 => [(1,3),(3,3),(5,3),(7,3)]
  | 43 => [(2,1),(2,3),(2,5),(4,1)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(6,5)]
  | 50 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(7,0)]
  | 55 => [(2,3),(2,5),(4,5)]
  | 56 => [(5,1),(5,4),(8,4)]
  | 57 => [(0,1),(1,4),(6,4)]
  | 58 => [(0,5),(1,2),(6,2)]
  | 59 => [(4,4),(8,4)]
  | _ => [(0,0),(6,4)]
def root7Node117Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(1,3),(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(0,4),(1,2),(6,2)]
  | 36 => some [(1,4),(3,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node117Domains1_fast_eq : root7Node117Domains1 = expandDomains root7Node117Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node117Domains1 v = expandDomains root7Node117Domains1Fast v from by decide) v
theorem root7Node117Step1Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root7Node117Domains0 root7Node117Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node117Domains0 root7Node117Domains1
    root7Node117Domains0Fast root7Node117Domains1Fast
    root7Node117Domains0_fast_eq root7Node117Domains1_fast_eq (by decide)
theorem root7Node117Step1_checked :
    checkReplacement table19 root7Node117Domains0 root7Node117Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node117Step1Chunk0_0_checked, root7Node117Step1Chunk0_1_checked, root7Node117Step1Chunk0_2_checked, root7Node117Step1Chunk0_3_checked, root7Node117Step1Chunk0_4_checked, root7Node117Step1Chunk0_5_checked, root7Node117Step1Chunk1_0_checked, root7Node117Step1Chunk1_1_checked, root7Node117Step1Chunk1_2_checked, root7Node117Step1Chunk1_3_checked, root7Node117Step1Chunk1_4_checked, root7Node117Step1Chunk1_5_checked, root7Node117Step1Chunk2_0_checked, root7Node117Step1Chunk2_1_checked, root7Node117Step1Chunk2_2_checked, root7Node117Step1Chunk2_3_checked, root7Node117Step1Chunk2_4_checked, root7Node117Step1Chunk2_5_checked, root7Node117Step1Chunk3_0_checked, root7Node117Step1Chunk3_1_checked, root7Node117Step1Chunk3_2_checked, root7Node117Step1Chunk3_3_checked, root7Node117Step1Chunk3_4_checked, root7Node117Step1Chunk3_5_checked, root7Node117Step1Chunk4_0_checked, root7Node117Step1Chunk4_1_checked, root7Node117Step1Chunk4_2_checked, root7Node117Step1Chunk4_3_checked, root7Node117Step1Chunk4_4_checked, root7Node117Step1Chunk4_5_checked, root7Node117Step1Chunk5_0_checked, root7Node117Step1Chunk5_1_checked, root7Node117Step1Chunk5_2_checked, root7Node117Step1Chunk5_3_checked, root7Node117Step1Chunk5_4_checked, root7Node117Step1Chunk5_5_checked, root7Node117Step1Chunk6_0_checked, root7Node117Step1Chunk6_1_checked, root7Node117Step1Chunk6_2_checked, root7Node117Step1Chunk6_3_checked, root7Node117Step1Chunk6_4_checked, root7Node117Step1Chunk6_5_checked, root7Node117Step1Chunk7_0_checked, root7Node117Step1Chunk7_1_checked, root7Node117Step1Chunk7_2_checked, root7Node117Step1Chunk7_3_checked, root7Node117Step1Chunk7_4_checked, root7Node117Step1Chunk7_5_checked, root7Node117Step1Chunk8_0_checked, root7Node117Step1Chunk8_1_checked, root7Node117Step1Chunk8_2_checked, root7Node117Step1Chunk8_3_checked, root7Node117Step1Chunk8_4_checked, root7Node117Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
