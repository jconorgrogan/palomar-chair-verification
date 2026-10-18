module

public import SpectreFinite.RadiusFourRoot6Part1
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable10
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node3Domains0 : Domains 61 State := restrict root6Node2Domains2 34 (3,1)
def root6Node3Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(4,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3)]
  | 59 => some [(8,2)]
  | _ => some [(5,0)]
theorem root6Node3Domains0_fast_eq : root6Node3Domains0 = expandDomains root6Node3Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node3Domains0 v = expandDomains root6Node3Domains0Fast v from by decide) v
theorem root6Node3Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node3Domains0 (.output 0) = true := by decide
def root6Node4Domains0 : Domains 61 State := restrict root6Node2Domains2 34 (7,1)
def root6Node4Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(4,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3)]
  | 59 => some [(8,2)]
  | _ => some [(5,0)]
theorem root6Node4Domains0_fast_eq : root6Node4Domains0 = expandDomains root6Node4Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node4Domains0 v = expandDomains root6Node4Domains0Fast v from by decide) v
theorem root6Node4Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node4Domains0 (.output 1) = true := by decide
def root6Node5Domains0 : Domains 61 State := restrict root6Node1Domains4 3 (8,4)
def root6Node5Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0),(1,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(1,5),(6,5)]
  | 10 => some [(0,4),(6,1)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(4,3),(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1),(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root6Node5Domains0_fast_eq : root6Node5Domains0 = expandDomains root6Node5Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node5Domains0 v = expandDomains root6Node5Domains0Fast v from by decide) v
def root6Node5Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(8,1)]
  | 9 => [(1,5)]
  | 10 => [(6,1)]
  | 11 => [(7,4)]
  | 12 => [(1,3)]
  | 13 => [(4,2)]
  | 14 => [(5,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(8,3)]
  | 18 => [(8,1)]
  | 19 => [(6,5)]
  | 20 => [(0,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(8,3)]
  | 27 => [(5,5)]
  | 28 => [(3,0)]
  | 29 => [(2,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0),(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3),(6,3)]
  | 59 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root6Node5Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root6Node5Domains1_fast_eq : root6Node5Domains1 = expandDomains root6Node5Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node5Domains1 v = expandDomains root6Node5Domains1Fast v from by decide) v
theorem root6Node5Step1Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root6Node5Domains0 root6Node5Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node5Domains0 root6Node5Domains1
    root6Node5Domains0Fast root6Node5Domains1Fast
    root6Node5Domains0_fast_eq root6Node5Domains1_fast_eq (by decide)
theorem root6Node5Step1_checked :
    checkReplacement table10 root6Node5Domains0 root6Node5Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node5Step1Chunk0_0_checked, root6Node5Step1Chunk0_1_checked, root6Node5Step1Chunk0_2_checked, root6Node5Step1Chunk0_3_checked, root6Node5Step1Chunk0_4_checked, root6Node5Step1Chunk0_5_checked, root6Node5Step1Chunk1_0_checked, root6Node5Step1Chunk1_1_checked, root6Node5Step1Chunk1_2_checked, root6Node5Step1Chunk1_3_checked, root6Node5Step1Chunk1_4_checked, root6Node5Step1Chunk1_5_checked, root6Node5Step1Chunk2_0_checked, root6Node5Step1Chunk2_1_checked, root6Node5Step1Chunk2_2_checked, root6Node5Step1Chunk2_3_checked, root6Node5Step1Chunk2_4_checked, root6Node5Step1Chunk2_5_checked, root6Node5Step1Chunk3_0_checked, root6Node5Step1Chunk3_1_checked, root6Node5Step1Chunk3_2_checked, root6Node5Step1Chunk3_3_checked, root6Node5Step1Chunk3_4_checked, root6Node5Step1Chunk3_5_checked, root6Node5Step1Chunk4_0_checked, root6Node5Step1Chunk4_1_checked, root6Node5Step1Chunk4_2_checked, root6Node5Step1Chunk4_3_checked, root6Node5Step1Chunk4_4_checked, root6Node5Step1Chunk4_5_checked, root6Node5Step1Chunk5_0_checked, root6Node5Step1Chunk5_1_checked, root6Node5Step1Chunk5_2_checked, root6Node5Step1Chunk5_3_checked, root6Node5Step1Chunk5_4_checked, root6Node5Step1Chunk5_5_checked, root6Node5Step1Chunk6_0_checked, root6Node5Step1Chunk6_1_checked, root6Node5Step1Chunk6_2_checked, root6Node5Step1Chunk6_3_checked, root6Node5Step1Chunk6_4_checked, root6Node5Step1Chunk6_5_checked, root6Node5Step1Chunk7_0_checked, root6Node5Step1Chunk7_1_checked, root6Node5Step1Chunk7_2_checked, root6Node5Step1Chunk7_3_checked, root6Node5Step1Chunk7_4_checked, root6Node5Step1Chunk7_5_checked, root6Node5Step1Chunk8_0_checked, root6Node5Step1Chunk8_1_checked, root6Node5Step1Chunk8_2_checked, root6Node5Step1Chunk8_3_checked, root6Node5Step1Chunk8_4_checked, root6Node5Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node6Domains0 : Domains 61 State := restrict root6Node5Domains1 42 (5,0)
def root6Node6Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root6Node6Domains0_fast_eq : root6Node6Domains0 = expandDomains root6Node6Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node6Domains0 v = expandDomains root6Node6Domains0Fast v from by decide) v
def root6Node6Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(8,1)]
  | 9 => [(1,5)]
  | 10 => [(6,1)]
  | 11 => [(7,4)]
  | 12 => [(1,3)]
  | 13 => [(4,2)]
  | 14 => [(5,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(8,3)]
  | 18 => [(8,1)]
  | 19 => [(6,5)]
  | 20 => [(0,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(8,3)]
  | 27 => [(5,5)]
  | 28 => [(3,0)]
  | 29 => [(2,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3)]
  | 59 => [(8,2)]
  | _ => [(5,0)]
def root6Node6Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3)]
  | 59 => some [(8,2)]
  | _ => some [(5,0)]
theorem root6Node6Domains1_fast_eq : root6Node6Domains1 = expandDomains root6Node6Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node6Domains1 v = expandDomains root6Node6Domains1Fast v from by decide) v
theorem root6Node6Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root6Node6Domains0 root6Node6Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node6Domains0 root6Node6Domains1
    root6Node6Domains0Fast root6Node6Domains1Fast
    root6Node6Domains0_fast_eq root6Node6Domains1_fast_eq (by decide)
theorem root6Node6Step1_checked :
    checkReplacement table39 root6Node6Domains0 root6Node6Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node6Step1Chunk0_0_checked, root6Node6Step1Chunk0_1_checked, root6Node6Step1Chunk0_2_checked, root6Node6Step1Chunk0_3_checked, root6Node6Step1Chunk0_4_checked, root6Node6Step1Chunk0_5_checked, root6Node6Step1Chunk1_0_checked, root6Node6Step1Chunk1_1_checked, root6Node6Step1Chunk1_2_checked, root6Node6Step1Chunk1_3_checked, root6Node6Step1Chunk1_4_checked, root6Node6Step1Chunk1_5_checked, root6Node6Step1Chunk2_0_checked, root6Node6Step1Chunk2_1_checked, root6Node6Step1Chunk2_2_checked, root6Node6Step1Chunk2_3_checked, root6Node6Step1Chunk2_4_checked, root6Node6Step1Chunk2_5_checked, root6Node6Step1Chunk3_0_checked, root6Node6Step1Chunk3_1_checked, root6Node6Step1Chunk3_2_checked, root6Node6Step1Chunk3_3_checked, root6Node6Step1Chunk3_4_checked, root6Node6Step1Chunk3_5_checked, root6Node6Step1Chunk4_0_checked, root6Node6Step1Chunk4_1_checked, root6Node6Step1Chunk4_2_checked, root6Node6Step1Chunk4_3_checked, root6Node6Step1Chunk4_4_checked, root6Node6Step1Chunk4_5_checked, root6Node6Step1Chunk5_0_checked, root6Node6Step1Chunk5_1_checked, root6Node6Step1Chunk5_2_checked, root6Node6Step1Chunk5_3_checked, root6Node6Step1Chunk5_4_checked, root6Node6Step1Chunk5_5_checked, root6Node6Step1Chunk6_0_checked, root6Node6Step1Chunk6_1_checked, root6Node6Step1Chunk6_2_checked, root6Node6Step1Chunk6_3_checked, root6Node6Step1Chunk6_4_checked, root6Node6Step1Chunk6_5_checked, root6Node6Step1Chunk7_0_checked, root6Node6Step1Chunk7_1_checked, root6Node6Step1Chunk7_2_checked, root6Node6Step1Chunk7_3_checked, root6Node6Step1Chunk7_4_checked, root6Node6Step1Chunk7_5_checked, root6Node6Step1Chunk8_0_checked, root6Node6Step1Chunk8_1_checked, root6Node6Step1Chunk8_2_checked, root6Node6Step1Chunk8_3_checked, root6Node6Step1Chunk8_4_checked, root6Node6Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node6Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node6Domains1 (.output 2) = true := by decide
def root6Node7Domains0 : Domains 61 State := restrict root6Node5Domains1 42 (8,0)
def root6Node7Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root6Node7Domains0_fast_eq : root6Node7Domains0 = expandDomains root6Node7Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node7Domains0 v = expandDomains root6Node7Domains0Fast v from by decide) v
def root6Node7Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(8,4)]
  | 4 => [(0,0)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(8,1)]
  | 9 => [(1,5)]
  | 10 => [(6,1)]
  | 11 => [(7,4)]
  | 12 => [(1,3)]
  | 13 => [(4,2)]
  | 14 => [(5,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(8,3)]
  | 18 => [(8,1)]
  | 19 => [(6,5)]
  | 20 => [(0,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(8,3)]
  | 27 => [(5,5)]
  | 28 => [(3,0)]
  | 29 => [(2,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3),(6,3)]
  | 59 => [(7,2),(8,2)]
  | _ => [(4,0),(8,0)]
def root6Node7Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(8,4)]
  | 4 => some [(0,0)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(1,5)]
  | 10 => some [(6,1)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(8,0)]
theorem root6Node7Domains1_fast_eq : root6Node7Domains1 = expandDomains root6Node7Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node7Domains1 v = expandDomains root6Node7Domains1Fast v from by decide) v
theorem root6Node7Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root6Node7Domains0 root6Node7Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node7Domains0 root6Node7Domains1
    root6Node7Domains0Fast root6Node7Domains1Fast
    root6Node7Domains0_fast_eq root6Node7Domains1_fast_eq (by decide)
theorem root6Node7Step1_checked :
    checkReplacement table39 root6Node7Domains0 root6Node7Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node7Step1Chunk0_0_checked, root6Node7Step1Chunk0_1_checked, root6Node7Step1Chunk0_2_checked, root6Node7Step1Chunk0_3_checked, root6Node7Step1Chunk0_4_checked, root6Node7Step1Chunk0_5_checked, root6Node7Step1Chunk1_0_checked, root6Node7Step1Chunk1_1_checked, root6Node7Step1Chunk1_2_checked, root6Node7Step1Chunk1_3_checked, root6Node7Step1Chunk1_4_checked, root6Node7Step1Chunk1_5_checked, root6Node7Step1Chunk2_0_checked, root6Node7Step1Chunk2_1_checked, root6Node7Step1Chunk2_2_checked, root6Node7Step1Chunk2_3_checked, root6Node7Step1Chunk2_4_checked, root6Node7Step1Chunk2_5_checked, root6Node7Step1Chunk3_0_checked, root6Node7Step1Chunk3_1_checked, root6Node7Step1Chunk3_2_checked, root6Node7Step1Chunk3_3_checked, root6Node7Step1Chunk3_4_checked, root6Node7Step1Chunk3_5_checked, root6Node7Step1Chunk4_0_checked, root6Node7Step1Chunk4_1_checked, root6Node7Step1Chunk4_2_checked, root6Node7Step1Chunk4_3_checked, root6Node7Step1Chunk4_4_checked, root6Node7Step1Chunk4_5_checked, root6Node7Step1Chunk5_0_checked, root6Node7Step1Chunk5_1_checked, root6Node7Step1Chunk5_2_checked, root6Node7Step1Chunk5_3_checked, root6Node7Step1Chunk5_4_checked, root6Node7Step1Chunk5_5_checked, root6Node7Step1Chunk6_0_checked, root6Node7Step1Chunk6_1_checked, root6Node7Step1Chunk6_2_checked, root6Node7Step1Chunk6_3_checked, root6Node7Step1Chunk6_4_checked, root6Node7Step1Chunk6_5_checked, root6Node7Step1Chunk7_0_checked, root6Node7Step1Chunk7_1_checked, root6Node7Step1Chunk7_2_checked, root6Node7Step1Chunk7_3_checked, root6Node7Step1Chunk7_4_checked, root6Node7Step1Chunk7_5_checked, root6Node7Step1Chunk8_0_checked, root6Node7Step1Chunk8_1_checked, root6Node7Step1Chunk8_2_checked, root6Node7Step1Chunk8_3_checked, root6Node7Step1Chunk8_4_checked, root6Node7Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
