module

public import SpectreFinite.RadiusFourRoot7Part28
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable38
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node88Domains0 : Domains 61 State := restrict root7Node86Domains1 42 (8,0)
def root7Node88Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(3,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(5,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5),(8,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(4,4),(7,2)]
  | _ => some [(1,4),(7,4)]
theorem root7Node88Domains0_fast_eq : root7Node88Domains0 = expandDomains root7Node88Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node88Domains0 v = expandDomains root7Node88Domains0Fast v from by decide) v
def root7Node89Domains0 : Domains 61 State := restrict root7Node88Domains0 50 (5,5)
def root7Node89Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(3,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5),(8,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(4,4),(7,2)]
  | _ => some [(1,4),(7,4)]
theorem root7Node89Domains0_fast_eq : root7Node89Domains0 = expandDomains root7Node89Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node89Domains0 v = expandDomains root7Node89Domains0Fast v from by decide) v
def root7Node89Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(3,5)]
  | 7 => [(0,3)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,4)]
  | 14 => [(1,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(7,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(1,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(5,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5)]
  | 54 => [(7,0)]
  | 55 => [(4,3)]
  | 56 => [(4,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(4,4)]
  | _ => [(1,4)]
def root7Node89Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(3,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(4,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(4,4)]
  | _ => some [(1,4)]
theorem root7Node89Domains1_fast_eq : root7Node89Domains1 = expandDomains root7Node89Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node89Domains1 v = expandDomains root7Node89Domains1Fast v from by decide) v
theorem root7Node89Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root7Node89Domains0 root7Node89Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node89Domains0 root7Node89Domains1
    root7Node89Domains0Fast root7Node89Domains1Fast
    root7Node89Domains0_fast_eq root7Node89Domains1_fast_eq (by decide)
theorem root7Node89Step1_checked :
    checkReplacement table46 root7Node89Domains0 root7Node89Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node89Step1Chunk0_0_checked, root7Node89Step1Chunk0_1_checked, root7Node89Step1Chunk0_2_checked, root7Node89Step1Chunk0_3_checked, root7Node89Step1Chunk0_4_checked, root7Node89Step1Chunk0_5_checked, root7Node89Step1Chunk1_0_checked, root7Node89Step1Chunk1_1_checked, root7Node89Step1Chunk1_2_checked, root7Node89Step1Chunk1_3_checked, root7Node89Step1Chunk1_4_checked, root7Node89Step1Chunk1_5_checked, root7Node89Step1Chunk2_0_checked, root7Node89Step1Chunk2_1_checked, root7Node89Step1Chunk2_2_checked, root7Node89Step1Chunk2_3_checked, root7Node89Step1Chunk2_4_checked, root7Node89Step1Chunk2_5_checked, root7Node89Step1Chunk3_0_checked, root7Node89Step1Chunk3_1_checked, root7Node89Step1Chunk3_2_checked, root7Node89Step1Chunk3_3_checked, root7Node89Step1Chunk3_4_checked, root7Node89Step1Chunk3_5_checked, root7Node89Step1Chunk4_0_checked, root7Node89Step1Chunk4_1_checked, root7Node89Step1Chunk4_2_checked, root7Node89Step1Chunk4_3_checked, root7Node89Step1Chunk4_4_checked, root7Node89Step1Chunk4_5_checked, root7Node89Step1Chunk5_0_checked, root7Node89Step1Chunk5_1_checked, root7Node89Step1Chunk5_2_checked, root7Node89Step1Chunk5_3_checked, root7Node89Step1Chunk5_4_checked, root7Node89Step1Chunk5_5_checked, root7Node89Step1Chunk6_0_checked, root7Node89Step1Chunk6_1_checked, root7Node89Step1Chunk6_2_checked, root7Node89Step1Chunk6_3_checked, root7Node89Step1Chunk6_4_checked, root7Node89Step1Chunk6_5_checked, root7Node89Step1Chunk7_0_checked, root7Node89Step1Chunk7_1_checked, root7Node89Step1Chunk7_2_checked, root7Node89Step1Chunk7_3_checked, root7Node89Step1Chunk7_4_checked, root7Node89Step1Chunk7_5_checked, root7Node89Step1Chunk8_0_checked, root7Node89Step1Chunk8_1_checked, root7Node89Step1Chunk8_2_checked, root7Node89Step1Chunk8_3_checked, root7Node89Step1Chunk8_4_checked, root7Node89Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node89Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node89Domains1 (.output 43) = true := by decide
def root7Node90Domains0 : Domains 61 State := restrict root7Node88Domains0 50 (8,5)
def root7Node90Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(3,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5),(8,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(4,4),(7,2)]
  | _ => some [(1,4),(7,4)]
theorem root7Node90Domains0_fast_eq : root7Node90Domains0 = expandDomains root7Node90Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node90Domains0 v = expandDomains root7Node90Domains0Fast v from by decide) v
def root7Node90Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(3,5)]
  | 7 => [(0,3)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,4)]
  | 14 => [(1,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(7,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(1,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(7,0)]
  | 55 => [(4,3)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(6,3)]
  | 59 => [(7,2)]
  | _ => [(7,4)]
def root7Node90Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(3,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(1,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(6,3)]
  | 59 => some [(7,2)]
  | _ => some [(7,4)]
theorem root7Node90Domains1_fast_eq : root7Node90Domains1 = expandDomains root7Node90Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node90Domains1 v = expandDomains root7Node90Domains1Fast v from by decide) v
theorem root7Node90Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root7Node90Domains0 root7Node90Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node90Domains0 root7Node90Domains1
    root7Node90Domains0Fast root7Node90Domains1Fast
    root7Node90Domains0_fast_eq root7Node90Domains1_fast_eq (by decide)
theorem root7Node90Step1_checked :
    checkReplacement table46 root7Node90Domains0 root7Node90Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node90Step1Chunk0_0_checked, root7Node90Step1Chunk0_1_checked, root7Node90Step1Chunk0_2_checked, root7Node90Step1Chunk0_3_checked, root7Node90Step1Chunk0_4_checked, root7Node90Step1Chunk0_5_checked, root7Node90Step1Chunk1_0_checked, root7Node90Step1Chunk1_1_checked, root7Node90Step1Chunk1_2_checked, root7Node90Step1Chunk1_3_checked, root7Node90Step1Chunk1_4_checked, root7Node90Step1Chunk1_5_checked, root7Node90Step1Chunk2_0_checked, root7Node90Step1Chunk2_1_checked, root7Node90Step1Chunk2_2_checked, root7Node90Step1Chunk2_3_checked, root7Node90Step1Chunk2_4_checked, root7Node90Step1Chunk2_5_checked, root7Node90Step1Chunk3_0_checked, root7Node90Step1Chunk3_1_checked, root7Node90Step1Chunk3_2_checked, root7Node90Step1Chunk3_3_checked, root7Node90Step1Chunk3_4_checked, root7Node90Step1Chunk3_5_checked, root7Node90Step1Chunk4_0_checked, root7Node90Step1Chunk4_1_checked, root7Node90Step1Chunk4_2_checked, root7Node90Step1Chunk4_3_checked, root7Node90Step1Chunk4_4_checked, root7Node90Step1Chunk4_5_checked, root7Node90Step1Chunk5_0_checked, root7Node90Step1Chunk5_1_checked, root7Node90Step1Chunk5_2_checked, root7Node90Step1Chunk5_3_checked, root7Node90Step1Chunk5_4_checked, root7Node90Step1Chunk5_5_checked, root7Node90Step1Chunk6_0_checked, root7Node90Step1Chunk6_1_checked, root7Node90Step1Chunk6_2_checked, root7Node90Step1Chunk6_3_checked, root7Node90Step1Chunk6_4_checked, root7Node90Step1Chunk6_5_checked, root7Node90Step1Chunk7_0_checked, root7Node90Step1Chunk7_1_checked, root7Node90Step1Chunk7_2_checked, root7Node90Step1Chunk7_3_checked, root7Node90Step1Chunk7_4_checked, root7Node90Step1Chunk7_5_checked, root7Node90Step1Chunk8_0_checked, root7Node90Step1Chunk8_1_checked, root7Node90Step1Chunk8_2_checked, root7Node90Step1Chunk8_3_checked, root7Node90Step1Chunk8_4_checked, root7Node90Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node90Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node90Domains1 (.output 44) = true := by decide
def root7Node91Domains0 : Domains 61 State := restrict root7Node85Domains1 35 (6,2)
def root7Node91Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(3,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(4,5),(5,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5),(8,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(4,4),(7,2)]
  | _ => some [(1,4),(7,4)]
theorem root7Node91Domains0_fast_eq : root7Node91Domains0 = expandDomains root7Node91Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node91Domains0 v = expandDomains root7Node91Domains0Fast v from by decide) v
def root7Node91Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(3,5)]
  | 7 => [(0,3)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,4)]
  | 14 => [(1,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(7,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0),(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(7,0)]
  | 55 => [(4,3)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(6,3)]
  | 59 => [(7,2)]
  | _ => [(1,4),(7,4)]
def root7Node91Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(3,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(6,3)]
  | 59 => some [(7,2)]
  | _ => some [(1,4),(7,4)]
theorem root7Node91Domains1_fast_eq : root7Node91Domains1 = expandDomains root7Node91Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node91Domains1 v = expandDomains root7Node91Domains1Fast v from by decide) v
theorem root7Node91Step1Chunk0_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk0_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk0_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk0_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk0_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk0_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk1_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk2_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk3_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk4_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk5_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk6_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk7_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_0⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_1⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_2⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_3⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_4⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1Chunk8_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_5⟩
      root7Node91Domains0 root7Node91Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains0 root7Node91Domains1
    root7Node91Domains0Fast root7Node91Domains1Fast
    root7Node91Domains0_fast_eq root7Node91Domains1_fast_eq (by decide)
theorem root7Node91Step1_checked :
    checkReplacement table38 root7Node91Domains0 root7Node91Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node91Step1Chunk0_0_checked, root7Node91Step1Chunk0_1_checked, root7Node91Step1Chunk0_2_checked, root7Node91Step1Chunk0_3_checked, root7Node91Step1Chunk0_4_checked, root7Node91Step1Chunk0_5_checked, root7Node91Step1Chunk1_0_checked, root7Node91Step1Chunk1_1_checked, root7Node91Step1Chunk1_2_checked, root7Node91Step1Chunk1_3_checked, root7Node91Step1Chunk1_4_checked, root7Node91Step1Chunk1_5_checked, root7Node91Step1Chunk2_0_checked, root7Node91Step1Chunk2_1_checked, root7Node91Step1Chunk2_2_checked, root7Node91Step1Chunk2_3_checked, root7Node91Step1Chunk2_4_checked, root7Node91Step1Chunk2_5_checked, root7Node91Step1Chunk3_0_checked, root7Node91Step1Chunk3_1_checked, root7Node91Step1Chunk3_2_checked, root7Node91Step1Chunk3_3_checked, root7Node91Step1Chunk3_4_checked, root7Node91Step1Chunk3_5_checked, root7Node91Step1Chunk4_0_checked, root7Node91Step1Chunk4_1_checked, root7Node91Step1Chunk4_2_checked, root7Node91Step1Chunk4_3_checked, root7Node91Step1Chunk4_4_checked, root7Node91Step1Chunk4_5_checked, root7Node91Step1Chunk5_0_checked, root7Node91Step1Chunk5_1_checked, root7Node91Step1Chunk5_2_checked, root7Node91Step1Chunk5_3_checked, root7Node91Step1Chunk5_4_checked, root7Node91Step1Chunk5_5_checked, root7Node91Step1Chunk6_0_checked, root7Node91Step1Chunk6_1_checked, root7Node91Step1Chunk6_2_checked, root7Node91Step1Chunk6_3_checked, root7Node91Step1Chunk6_4_checked, root7Node91Step1Chunk6_5_checked, root7Node91Step1Chunk7_0_checked, root7Node91Step1Chunk7_1_checked, root7Node91Step1Chunk7_2_checked, root7Node91Step1Chunk7_3_checked, root7Node91Step1Chunk7_4_checked, root7Node91Step1Chunk7_5_checked, root7Node91Step1Chunk8_0_checked, root7Node91Step1Chunk8_1_checked, root7Node91Step1Chunk8_2_checked, root7Node91Step1Chunk8_3_checked, root7Node91Step1Chunk8_4_checked, root7Node91Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node91Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(4,3)]
  | 6 => [(3,5)]
  | 7 => [(0,3)]
  | 8 => [(4,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,4)]
  | 14 => [(1,3)]
  | 15 => [(5,2)]
  | 16 => [(8,0)]
  | 17 => [(8,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(7,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(7,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(7,0)]
  | 55 => [(4,3)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(6,3)]
  | 59 => [(7,2)]
  | _ => [(7,4)]
def root7Node91Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(3,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(5,2)]
  | 16 => some [(8,0)]
  | 17 => some [(8,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(7,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(6,3)]
  | 59 => some [(7,2)]
  | _ => some [(7,4)]
theorem root7Node91Domains2_fast_eq : root7Node91Domains2 = expandDomains root7Node91Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node91Domains2 v = expandDomains root7Node91Domains2Fast v from by decide) v
theorem root7Node91Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node91Domains1 root7Node91Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node91Domains1 root7Node91Domains2
    root7Node91Domains1Fast root7Node91Domains2Fast
    root7Node91Domains1_fast_eq root7Node91Domains2_fast_eq (by decide)
theorem root7Node91Step2_checked :
    checkReplacement table39 root7Node91Domains1 root7Node91Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node91Step2Chunk0_0_checked, root7Node91Step2Chunk0_1_checked, root7Node91Step2Chunk0_2_checked, root7Node91Step2Chunk0_3_checked, root7Node91Step2Chunk0_4_checked, root7Node91Step2Chunk0_5_checked, root7Node91Step2Chunk1_0_checked, root7Node91Step2Chunk1_1_checked, root7Node91Step2Chunk1_2_checked, root7Node91Step2Chunk1_3_checked, root7Node91Step2Chunk1_4_checked, root7Node91Step2Chunk1_5_checked, root7Node91Step2Chunk2_0_checked, root7Node91Step2Chunk2_1_checked, root7Node91Step2Chunk2_2_checked, root7Node91Step2Chunk2_3_checked, root7Node91Step2Chunk2_4_checked, root7Node91Step2Chunk2_5_checked, root7Node91Step2Chunk3_0_checked, root7Node91Step2Chunk3_1_checked, root7Node91Step2Chunk3_2_checked, root7Node91Step2Chunk3_3_checked, root7Node91Step2Chunk3_4_checked, root7Node91Step2Chunk3_5_checked, root7Node91Step2Chunk4_0_checked, root7Node91Step2Chunk4_1_checked, root7Node91Step2Chunk4_2_checked, root7Node91Step2Chunk4_3_checked, root7Node91Step2Chunk4_4_checked, root7Node91Step2Chunk4_5_checked, root7Node91Step2Chunk5_0_checked, root7Node91Step2Chunk5_1_checked, root7Node91Step2Chunk5_2_checked, root7Node91Step2Chunk5_3_checked, root7Node91Step2Chunk5_4_checked, root7Node91Step2Chunk5_5_checked, root7Node91Step2Chunk6_0_checked, root7Node91Step2Chunk6_1_checked, root7Node91Step2Chunk6_2_checked, root7Node91Step2Chunk6_3_checked, root7Node91Step2Chunk6_4_checked, root7Node91Step2Chunk6_5_checked, root7Node91Step2Chunk7_0_checked, root7Node91Step2Chunk7_1_checked, root7Node91Step2Chunk7_2_checked, root7Node91Step2Chunk7_3_checked, root7Node91Step2Chunk7_4_checked, root7Node91Step2Chunk7_5_checked, root7Node91Step2Chunk8_0_checked, root7Node91Step2Chunk8_1_checked, root7Node91Step2Chunk8_2_checked, root7Node91Step2Chunk8_3_checked, root7Node91Step2Chunk8_4_checked, root7Node91Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node91Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node91Domains2 (.output 45) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
