module

public import SpectreFinite.RadiusFourRoot0Part7
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable14
public import SpectreFinite.RadiusFourTable2

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node19Domains0 : Domains 61 State := restrict root0Node18Domains1 17 (5,1)
def root0Node19Domains0Fast (v : Fin 61) : Option (List State) :=
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
theorem root0Node19Domains0_fast_eq : root0Node19Domains0 = expandDomains root0Node19Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node19Domains0 v = expandDomains root0Node19Domains0Fast v from by decide) v
theorem root0Node19Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node19Domains0 (.output 8) = true := by decide
def root0Node20Domains0 : Domains 61 State := restrict root0Node18Domains1 17 (8,1)
def root0Node20Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 17 => some [(8,1)]
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
theorem root0Node20Domains0_fast_eq : root0Node20Domains0 = expandDomains root0Node20Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node20Domains0 v = expandDomains root0Node20Domains0Fast v from by decide) v
theorem root0Node20Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node20Domains0 (.output 9) = true := by decide
def root0Node21Domains0 : Domains 61 State := restrict root0Node13Domains4 0 (8,0)
def root0Node21Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
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
theorem root0Node21Domains0_fast_eq : root0Node21Domains0 = expandDomains root0Node21Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node21Domains0 v = expandDomains root0Node21Domains0Fast v from by decide) v
def root0Node21Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0),(3,0)]
  | 4 => [(2,1),(2,5)]
  | 5 => [(5,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2),(7,2)]
  | 11 => [(4,3)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
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
def root0Node21Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0),(3,0)]
  | 4 => some [(2,1),(2,5)]
  | 5 => some [(5,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2),(7,2)]
  | 11 => some [(4,3)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
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
theorem root0Node21Domains1_fast_eq : root0Node21Domains1 = expandDomains root0Node21Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node21Domains1 v = expandDomains root0Node21Domains1Fast v from by decide) v
theorem root0Node21Step1Chunk0_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk0_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk0_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk0_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk0_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk0_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk1_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk2_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk3_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk4_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk5_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk6_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk7_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_0⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_1⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_2⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_3⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_4⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1Chunk8_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_5⟩
      root0Node21Domains0 root0Node21Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node21Domains0 root0Node21Domains1
    root0Node21Domains0Fast root0Node21Domains1Fast
    root0Node21Domains0_fast_eq root0Node21Domains1_fast_eq (by decide)
theorem root0Node21Step1_checked :
    checkReplacement table14 root0Node21Domains0 root0Node21Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node21Step1Chunk0_0_checked, root0Node21Step1Chunk0_1_checked, root0Node21Step1Chunk0_2_checked, root0Node21Step1Chunk0_3_checked, root0Node21Step1Chunk0_4_checked, root0Node21Step1Chunk0_5_checked, root0Node21Step1Chunk1_0_checked, root0Node21Step1Chunk1_1_checked, root0Node21Step1Chunk1_2_checked, root0Node21Step1Chunk1_3_checked, root0Node21Step1Chunk1_4_checked, root0Node21Step1Chunk1_5_checked, root0Node21Step1Chunk2_0_checked, root0Node21Step1Chunk2_1_checked, root0Node21Step1Chunk2_2_checked, root0Node21Step1Chunk2_3_checked, root0Node21Step1Chunk2_4_checked, root0Node21Step1Chunk2_5_checked, root0Node21Step1Chunk3_0_checked, root0Node21Step1Chunk3_1_checked, root0Node21Step1Chunk3_2_checked, root0Node21Step1Chunk3_3_checked, root0Node21Step1Chunk3_4_checked, root0Node21Step1Chunk3_5_checked, root0Node21Step1Chunk4_0_checked, root0Node21Step1Chunk4_1_checked, root0Node21Step1Chunk4_2_checked, root0Node21Step1Chunk4_3_checked, root0Node21Step1Chunk4_4_checked, root0Node21Step1Chunk4_5_checked, root0Node21Step1Chunk5_0_checked, root0Node21Step1Chunk5_1_checked, root0Node21Step1Chunk5_2_checked, root0Node21Step1Chunk5_3_checked, root0Node21Step1Chunk5_4_checked, root0Node21Step1Chunk5_5_checked, root0Node21Step1Chunk6_0_checked, root0Node21Step1Chunk6_1_checked, root0Node21Step1Chunk6_2_checked, root0Node21Step1Chunk6_3_checked, root0Node21Step1Chunk6_4_checked, root0Node21Step1Chunk6_5_checked, root0Node21Step1Chunk7_0_checked, root0Node21Step1Chunk7_1_checked, root0Node21Step1Chunk7_2_checked, root0Node21Step1Chunk7_3_checked, root0Node21Step1Chunk7_4_checked, root0Node21Step1Chunk7_5_checked, root0Node21Step1Chunk8_0_checked, root0Node21Step1Chunk8_1_checked, root0Node21Step1Chunk8_2_checked, root0Node21Step1Chunk8_3_checked, root0Node21Step1Chunk8_4_checked, root0Node21Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node22Domains0 : Domains 61 State := restrict root0Node21Domains1 3 (1,0)
def root0Node22Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0)]
  | 4 => some [(2,1),(2,5)]
  | 5 => some [(5,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2),(7,2)]
  | 11 => some [(4,3)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
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
theorem root0Node22Domains0_fast_eq : root0Node22Domains0 = expandDomains root0Node22Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node22Domains0 v = expandDomains root0Node22Domains0Fast v from by decide) v
def root0Node22Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(1,0)]
  | 4 => [(2,1)]
  | 5 => [(5,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(3,2)]
  | 11 => [(4,3)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
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
def root0Node22Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(1,0)]
  | 4 => some [(2,1)]
  | 5 => some [(5,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2)]
  | 11 => some [(4,3)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
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
theorem root0Node22Domains1_fast_eq : root0Node22Domains1 = expandDomains root0Node22Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node22Domains1 v = expandDomains root0Node22Domains1Fast v from by decide) v
theorem root0Node22Step1Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root0Node22Domains0 root0Node22Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node22Domains0 root0Node22Domains1
    root0Node22Domains0Fast root0Node22Domains1Fast
    root0Node22Domains0_fast_eq root0Node22Domains1_fast_eq (by decide)
theorem root0Node22Step1_checked :
    checkReplacement table2 root0Node22Domains0 root0Node22Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node22Step1Chunk0_0_checked, root0Node22Step1Chunk0_1_checked, root0Node22Step1Chunk0_2_checked, root0Node22Step1Chunk0_3_checked, root0Node22Step1Chunk0_4_checked, root0Node22Step1Chunk0_5_checked, root0Node22Step1Chunk1_0_checked, root0Node22Step1Chunk1_1_checked, root0Node22Step1Chunk1_2_checked, root0Node22Step1Chunk1_3_checked, root0Node22Step1Chunk1_4_checked, root0Node22Step1Chunk1_5_checked, root0Node22Step1Chunk2_0_checked, root0Node22Step1Chunk2_1_checked, root0Node22Step1Chunk2_2_checked, root0Node22Step1Chunk2_3_checked, root0Node22Step1Chunk2_4_checked, root0Node22Step1Chunk2_5_checked, root0Node22Step1Chunk3_0_checked, root0Node22Step1Chunk3_1_checked, root0Node22Step1Chunk3_2_checked, root0Node22Step1Chunk3_3_checked, root0Node22Step1Chunk3_4_checked, root0Node22Step1Chunk3_5_checked, root0Node22Step1Chunk4_0_checked, root0Node22Step1Chunk4_1_checked, root0Node22Step1Chunk4_2_checked, root0Node22Step1Chunk4_3_checked, root0Node22Step1Chunk4_4_checked, root0Node22Step1Chunk4_5_checked, root0Node22Step1Chunk5_0_checked, root0Node22Step1Chunk5_1_checked, root0Node22Step1Chunk5_2_checked, root0Node22Step1Chunk5_3_checked, root0Node22Step1Chunk5_4_checked, root0Node22Step1Chunk5_5_checked, root0Node22Step1Chunk6_0_checked, root0Node22Step1Chunk6_1_checked, root0Node22Step1Chunk6_2_checked, root0Node22Step1Chunk6_3_checked, root0Node22Step1Chunk6_4_checked, root0Node22Step1Chunk6_5_checked, root0Node22Step1Chunk7_0_checked, root0Node22Step1Chunk7_1_checked, root0Node22Step1Chunk7_2_checked, root0Node22Step1Chunk7_3_checked, root0Node22Step1Chunk7_4_checked, root0Node22Step1Chunk7_5_checked, root0Node22Step1Chunk8_0_checked, root0Node22Step1Chunk8_1_checked, root0Node22Step1Chunk8_2_checked, root0Node22Step1Chunk8_3_checked, root0Node22Step1Chunk8_4_checked, root0Node22Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node22Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node22Domains1 (.output 10) = true := by decide
def root0Node23Domains0 : Domains 61 State := restrict root0Node21Domains1 3 (3,0)
def root0Node23Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(3,0)]
  | 4 => some [(2,1),(2,5)]
  | 5 => some [(5,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(3,2),(7,2)]
  | 11 => some [(4,3)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
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
theorem root0Node23Domains0_fast_eq : root0Node23Domains0 = expandDomains root0Node23Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node23Domains0 v = expandDomains root0Node23Domains0Fast v from by decide) v
def root0Node23Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,0)]
  | 1 => [(8,3)]
  | 2 => [(5,5)]
  | 3 => [(3,0)]
  | 4 => [(2,5)]
  | 5 => [(5,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(4,4)]
  | 9 => [(0,0)]
  | 10 => [(7,2)]
  | 11 => [(4,3)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
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
def root0Node23Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,0)]
  | 1 => some [(8,3)]
  | 2 => some [(5,5)]
  | 3 => some [(3,0)]
  | 4 => some [(2,5)]
  | 5 => some [(5,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(4,4)]
  | 9 => some [(0,0)]
  | 10 => some [(7,2)]
  | 11 => some [(4,3)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
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
theorem root0Node23Domains1_fast_eq : root0Node23Domains1 = expandDomains root0Node23Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node23Domains1 v = expandDomains root0Node23Domains1Fast v from by decide) v
theorem root0Node23Step1Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1_checked :
    checkReplacement table2 root0Node23Domains0 root0Node23Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node23Step1Chunk0_0_checked, root0Node23Step1Chunk0_1_checked, root0Node23Step1Chunk0_2_checked, root0Node23Step1Chunk0_3_checked, root0Node23Step1Chunk0_4_checked, root0Node23Step1Chunk0_5_checked, root0Node23Step1Chunk1_0_checked, root0Node23Step1Chunk1_1_checked, root0Node23Step1Chunk1_2_checked, root0Node23Step1Chunk1_3_checked, root0Node23Step1Chunk1_4_checked, root0Node23Step1Chunk1_5_checked, root0Node23Step1Chunk2_0_checked, root0Node23Step1Chunk2_1_checked, root0Node23Step1Chunk2_2_checked, root0Node23Step1Chunk2_3_checked, root0Node23Step1Chunk2_4_checked, root0Node23Step1Chunk2_5_checked, root0Node23Step1Chunk3_0_checked, root0Node23Step1Chunk3_1_checked, root0Node23Step1Chunk3_2_checked, root0Node23Step1Chunk3_3_checked, root0Node23Step1Chunk3_4_checked, root0Node23Step1Chunk3_5_checked, root0Node23Step1Chunk4_0_checked, root0Node23Step1Chunk4_1_checked, root0Node23Step1Chunk4_2_checked, root0Node23Step1Chunk4_3_checked, root0Node23Step1Chunk4_4_checked, root0Node23Step1Chunk4_5_checked, root0Node23Step1Chunk5_0_checked, root0Node23Step1Chunk5_1_checked, root0Node23Step1Chunk5_2_checked, root0Node23Step1Chunk5_3_checked, root0Node23Step1Chunk5_4_checked, root0Node23Step1Chunk5_5_checked, root0Node23Step1Chunk6_0_checked, root0Node23Step1Chunk6_1_checked, root0Node23Step1Chunk6_2_checked, root0Node23Step1Chunk6_3_checked, root0Node23Step1Chunk6_4_checked, root0Node23Step1Chunk6_5_checked, root0Node23Step1Chunk7_0_checked, root0Node23Step1Chunk7_1_checked, root0Node23Step1Chunk7_2_checked, root0Node23Step1Chunk7_3_checked, root0Node23Step1Chunk7_4_checked, root0Node23Step1Chunk7_5_checked, root0Node23Step1Chunk8_0_checked, root0Node23Step1Chunk8_1_checked, root0Node23Step1Chunk8_2_checked, root0Node23Step1Chunk8_3_checked, root0Node23Step1Chunk8_4_checked, root0Node23Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node23Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node23Domains1 (.output 11) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
