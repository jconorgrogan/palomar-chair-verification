module

public import SpectreFinite.RadiusFourRoot7Part4
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable31
public import SpectreFinite.RadiusFourTable38

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node10Domains0 : Domains 61 State := restrict root7Node9Domains2 35 (1,2)
def root7Node10Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(6,3)]
  | 41 => some [(7,2),(8,2)]
  | 42 => some [(4,0),(5,0),(8,0)]
  | 43 => some [(2,1),(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(4,1),(8,1)]
  | 47 => some [(0,2),(6,5)]
  | 48 => some [(0,4),(1,1)]
  | 49 => some [(5,1),(5,4)]
  | 50 => some [(3,2),(5,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5)]
  | 54 => some [(7,0),(8,0)]
  | 55 => some [(4,3),(8,3)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4)]
  | 58 => some [(0,5),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(1,4)]
theorem root7Node10Domains0_fast_eq : root7Node10Domains0 = expandDomains root7Node10Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node10Domains0 v = expandDomains root7Node10Domains0Fast v from by decide) v
def root7Node10Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,1)]
  | 1 => [(0,2)]
  | 2 => [(1,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(5,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(1,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(8,2)]
  | 42 => [(4,0),(5,0),(8,0)]
  | 43 => [(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,1),(5,4)]
  | 50 => [(5,2)]
  | 51 => [(8,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(7,0)]
  | 55 => [(4,3),(8,3)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(1,4)]
def root7Node10Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(4,0),(5,0),(8,0)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,1),(5,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3),(8,3)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(1,4)]
theorem root7Node10Domains1_fast_eq : root7Node10Domains1 = expandDomains root7Node10Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node10Domains1 v = expandDomains root7Node10Domains1Fast v from by decide) v
theorem root7Node10Step1Chunk0_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_0⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk0_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_1⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk0_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_2⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk0_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_3⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk0_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_4⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk0_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_5⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk1_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_0⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk1_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_1⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk1_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_2⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk1_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_3⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk1_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_4⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk1_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_5⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk2_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_0⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk2_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_1⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk2_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_2⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk2_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_3⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk2_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_4⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk2_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_5⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk3_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_0⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk3_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_1⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk3_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_2⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk3_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_3⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk3_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_4⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk3_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_5⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk4_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_0⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk4_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_1⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk4_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_2⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk4_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_3⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk4_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_4⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk4_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_5⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk5_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_0⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk5_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_1⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk5_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_2⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk5_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_3⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk5_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_4⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk5_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_5⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk6_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_0⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk6_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_1⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk6_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_2⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk6_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_3⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk6_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_4⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk6_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_5⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk7_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_0⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk7_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_1⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk7_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_2⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk7_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_3⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk7_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_4⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk7_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_5⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk8_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_0⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk8_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_1⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk8_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_2⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk8_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_3⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk8_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_4⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1Chunk8_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_5⟩
      root7Node10Domains0 root7Node10Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains0 root7Node10Domains1
    root7Node10Domains0Fast root7Node10Domains1Fast
    root7Node10Domains0_fast_eq root7Node10Domains1_fast_eq (by decide)
theorem root7Node10Step1_checked :
    checkReplacement table38 root7Node10Domains0 root7Node10Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node10Step1Chunk0_0_checked, root7Node10Step1Chunk0_1_checked, root7Node10Step1Chunk0_2_checked, root7Node10Step1Chunk0_3_checked, root7Node10Step1Chunk0_4_checked, root7Node10Step1Chunk0_5_checked, root7Node10Step1Chunk1_0_checked, root7Node10Step1Chunk1_1_checked, root7Node10Step1Chunk1_2_checked, root7Node10Step1Chunk1_3_checked, root7Node10Step1Chunk1_4_checked, root7Node10Step1Chunk1_5_checked, root7Node10Step1Chunk2_0_checked, root7Node10Step1Chunk2_1_checked, root7Node10Step1Chunk2_2_checked, root7Node10Step1Chunk2_3_checked, root7Node10Step1Chunk2_4_checked, root7Node10Step1Chunk2_5_checked, root7Node10Step1Chunk3_0_checked, root7Node10Step1Chunk3_1_checked, root7Node10Step1Chunk3_2_checked, root7Node10Step1Chunk3_3_checked, root7Node10Step1Chunk3_4_checked, root7Node10Step1Chunk3_5_checked, root7Node10Step1Chunk4_0_checked, root7Node10Step1Chunk4_1_checked, root7Node10Step1Chunk4_2_checked, root7Node10Step1Chunk4_3_checked, root7Node10Step1Chunk4_4_checked, root7Node10Step1Chunk4_5_checked, root7Node10Step1Chunk5_0_checked, root7Node10Step1Chunk5_1_checked, root7Node10Step1Chunk5_2_checked, root7Node10Step1Chunk5_3_checked, root7Node10Step1Chunk5_4_checked, root7Node10Step1Chunk5_5_checked, root7Node10Step1Chunk6_0_checked, root7Node10Step1Chunk6_1_checked, root7Node10Step1Chunk6_2_checked, root7Node10Step1Chunk6_3_checked, root7Node10Step1Chunk6_4_checked, root7Node10Step1Chunk6_5_checked, root7Node10Step1Chunk7_0_checked, root7Node10Step1Chunk7_1_checked, root7Node10Step1Chunk7_2_checked, root7Node10Step1Chunk7_3_checked, root7Node10Step1Chunk7_4_checked, root7Node10Step1Chunk7_5_checked, root7Node10Step1Chunk8_0_checked, root7Node10Step1Chunk8_1_checked, root7Node10Step1Chunk8_2_checked, root7Node10Step1Chunk8_3_checked, root7Node10Step1Chunk8_4_checked, root7Node10Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node10Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(4,1)]
  | 1 => [(0,2)]
  | 2 => [(1,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(7,3)]
  | 6 => [(5,2)]
  | 7 => [(5,0)]
  | 8 => [(4,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(6,4)]
  | 12 => [(1,2)]
  | 13 => [(8,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(0,3)]
  | 20 => [(8,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,3)]
  | 27 => [(4,2)]
  | 28 => [(5,3)]
  | 29 => [(8,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(1,2)]
  | 36 => [(7,4)]
  | 37 => [(6,3)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0),(8,0)]
  | 43 => [(4,1)]
  | 44 => [(0,2)]
  | 45 => [(1,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(5,2)]
  | 51 => [(8,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(7,0)]
  | 55 => [(4,3)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(1,4)]
def root7Node10Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(1,4)]
theorem root7Node10Domains2_fast_eq : root7Node10Domains2 = expandDomains root7Node10Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node10Domains2 v = expandDomains root7Node10Domains2Fast v from by decide) v
theorem root7Node10Step2Chunk0_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_0⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk0_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_1⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk0_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_2⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk0_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_3⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk0_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_4⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk0_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_5⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk1_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_0⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk1_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_1⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk1_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_2⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk1_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_3⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk1_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_4⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk1_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_5⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk2_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_0⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk2_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_1⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk2_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_2⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk2_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_3⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk2_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_4⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk2_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_5⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk3_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_0⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk3_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_1⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk3_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_2⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk3_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_3⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk3_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_4⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk3_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_5⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk4_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_0⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk4_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_1⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk4_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_2⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk4_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_3⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk4_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_4⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk4_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_5⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk5_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_0⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk5_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_1⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk5_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_2⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk5_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_3⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk5_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_4⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk5_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_5⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk6_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_0⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk6_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_1⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk6_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_2⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk6_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_3⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk6_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_4⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk6_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_5⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk7_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_0⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk7_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_1⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk7_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_2⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk7_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_3⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk7_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_4⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk7_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_5⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk8_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_0⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk8_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_1⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk8_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_2⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk8_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_3⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk8_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_4⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2Chunk8_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_5⟩
      root7Node10Domains1 root7Node10Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node10Domains1 root7Node10Domains2
    root7Node10Domains1Fast root7Node10Domains2Fast
    root7Node10Domains1_fast_eq root7Node10Domains2_fast_eq (by decide)
theorem root7Node10Step2_checked :
    checkReplacement table31 root7Node10Domains1 root7Node10Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node10Step2Chunk0_0_checked, root7Node10Step2Chunk0_1_checked, root7Node10Step2Chunk0_2_checked, root7Node10Step2Chunk0_3_checked, root7Node10Step2Chunk0_4_checked, root7Node10Step2Chunk0_5_checked, root7Node10Step2Chunk1_0_checked, root7Node10Step2Chunk1_1_checked, root7Node10Step2Chunk1_2_checked, root7Node10Step2Chunk1_3_checked, root7Node10Step2Chunk1_4_checked, root7Node10Step2Chunk1_5_checked, root7Node10Step2Chunk2_0_checked, root7Node10Step2Chunk2_1_checked, root7Node10Step2Chunk2_2_checked, root7Node10Step2Chunk2_3_checked, root7Node10Step2Chunk2_4_checked, root7Node10Step2Chunk2_5_checked, root7Node10Step2Chunk3_0_checked, root7Node10Step2Chunk3_1_checked, root7Node10Step2Chunk3_2_checked, root7Node10Step2Chunk3_3_checked, root7Node10Step2Chunk3_4_checked, root7Node10Step2Chunk3_5_checked, root7Node10Step2Chunk4_0_checked, root7Node10Step2Chunk4_1_checked, root7Node10Step2Chunk4_2_checked, root7Node10Step2Chunk4_3_checked, root7Node10Step2Chunk4_4_checked, root7Node10Step2Chunk4_5_checked, root7Node10Step2Chunk5_0_checked, root7Node10Step2Chunk5_1_checked, root7Node10Step2Chunk5_2_checked, root7Node10Step2Chunk5_3_checked, root7Node10Step2Chunk5_4_checked, root7Node10Step2Chunk5_5_checked, root7Node10Step2Chunk6_0_checked, root7Node10Step2Chunk6_1_checked, root7Node10Step2Chunk6_2_checked, root7Node10Step2Chunk6_3_checked, root7Node10Step2Chunk6_4_checked, root7Node10Step2Chunk6_5_checked, root7Node10Step2Chunk7_0_checked, root7Node10Step2Chunk7_1_checked, root7Node10Step2Chunk7_2_checked, root7Node10Step2Chunk7_3_checked, root7Node10Step2Chunk7_4_checked, root7Node10Step2Chunk7_5_checked, root7Node10Step2Chunk8_0_checked, root7Node10Step2Chunk8_1_checked, root7Node10Step2Chunk8_2_checked, root7Node10Step2Chunk8_3_checked, root7Node10Step2Chunk8_4_checked, root7Node10Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node11Domains0 : Domains 61 State := restrict root7Node10Domains2 42 (5,0)
def root7Node11Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(1,4)]
theorem root7Node11Domains0_fast_eq : root7Node11Domains0 = expandDomains root7Node11Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node11Domains0 v = expandDomains root7Node11Domains0Fast v from by decide) v
def root7Node12Domains0 : Domains 61 State := restrict root7Node11Domains0 56 (5,4)
def root7Node12Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(5,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(1,4)]
theorem root7Node12Domains0_fast_eq : root7Node12Domains0 = expandDomains root7Node12Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node12Domains0 v = expandDomains root7Node12Domains0Fast v from by decide) v
theorem root7Node12Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node12Domains0 (.output 3) = true := by decide
def root7Node13Domains0 : Domains 61 State := restrict root7Node11Domains0 56 (8,4)
def root7Node13Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(4,1)]
  | 1 => some [(0,2)]
  | 2 => some [(1,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(7,3)]
  | 6 => some [(5,2)]
  | 7 => some [(5,0)]
  | 8 => some [(4,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(6,4)]
  | 12 => some [(1,2)]
  | 13 => some [(8,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(0,3)]
  | 20 => some [(8,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,3)]
  | 27 => some [(4,2)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(7,4)]
  | 37 => some [(6,3)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0)]
  | 43 => some [(4,1)]
  | 44 => some [(0,2)]
  | 45 => some [(1,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(5,2)]
  | 51 => some [(8,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(1,4)]
theorem root7Node13Domains0_fast_eq : root7Node13Domains0 = expandDomains root7Node13Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node13Domains0 v = expandDomains root7Node13Domains0Fast v from by decide) v
theorem root7Node13Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node13Domains0 (.output 4) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
