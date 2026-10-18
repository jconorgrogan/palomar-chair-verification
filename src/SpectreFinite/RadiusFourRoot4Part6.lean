module

public import SpectreFinite.RadiusFourRoot4Part5
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable40
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node16Domains0 : Domains 61 State := restrict root4Node15Domains1 52 (1,3)
def root4Node16Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0)]
  | 20 => some [(2,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0)]
  | 29 => some [(3,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root4Node16Domains0_fast_eq : root4Node16Domains0 = expandDomains root4Node16Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node16Domains0 v = expandDomains root4Node16Domains0Fast v from by decide) v
def root4Node16Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(1,0)]
  | 20 => [(2,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(0,0)]
  | 29 => [(3,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(7,3)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(6,4)]
  | 43 => [(4,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(8,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3)]
  | 56 => [(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(5,4)]
  | _ => [(6,4)]
def root4Node16Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0)]
  | 20 => some [(2,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0)]
  | 29 => some [(3,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(8,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(5,4)]
  | _ => some [(6,4)]
theorem root4Node16Domains1_fast_eq : root4Node16Domains1 = expandDomains root4Node16Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node16Domains1 v = expandDomains root4Node16Domains1Fast v from by decide) v
theorem root4Node16Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root4Node16Domains0 root4Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node16Domains0 root4Node16Domains1
    root4Node16Domains0Fast root4Node16Domains1Fast
    root4Node16Domains0_fast_eq root4Node16Domains1_fast_eq (by decide)
theorem root4Node16Step1_checked :
    checkReplacement table46 root4Node16Domains0 root4Node16Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node16Step1Chunk0_0_checked, root4Node16Step1Chunk0_1_checked, root4Node16Step1Chunk0_2_checked, root4Node16Step1Chunk0_3_checked, root4Node16Step1Chunk0_4_checked, root4Node16Step1Chunk0_5_checked, root4Node16Step1Chunk1_0_checked, root4Node16Step1Chunk1_1_checked, root4Node16Step1Chunk1_2_checked, root4Node16Step1Chunk1_3_checked, root4Node16Step1Chunk1_4_checked, root4Node16Step1Chunk1_5_checked, root4Node16Step1Chunk2_0_checked, root4Node16Step1Chunk2_1_checked, root4Node16Step1Chunk2_2_checked, root4Node16Step1Chunk2_3_checked, root4Node16Step1Chunk2_4_checked, root4Node16Step1Chunk2_5_checked, root4Node16Step1Chunk3_0_checked, root4Node16Step1Chunk3_1_checked, root4Node16Step1Chunk3_2_checked, root4Node16Step1Chunk3_3_checked, root4Node16Step1Chunk3_4_checked, root4Node16Step1Chunk3_5_checked, root4Node16Step1Chunk4_0_checked, root4Node16Step1Chunk4_1_checked, root4Node16Step1Chunk4_2_checked, root4Node16Step1Chunk4_3_checked, root4Node16Step1Chunk4_4_checked, root4Node16Step1Chunk4_5_checked, root4Node16Step1Chunk5_0_checked, root4Node16Step1Chunk5_1_checked, root4Node16Step1Chunk5_2_checked, root4Node16Step1Chunk5_3_checked, root4Node16Step1Chunk5_4_checked, root4Node16Step1Chunk5_5_checked, root4Node16Step1Chunk6_0_checked, root4Node16Step1Chunk6_1_checked, root4Node16Step1Chunk6_2_checked, root4Node16Step1Chunk6_3_checked, root4Node16Step1Chunk6_4_checked, root4Node16Step1Chunk6_5_checked, root4Node16Step1Chunk7_0_checked, root4Node16Step1Chunk7_1_checked, root4Node16Step1Chunk7_2_checked, root4Node16Step1Chunk7_3_checked, root4Node16Step1Chunk7_4_checked, root4Node16Step1Chunk7_5_checked, root4Node16Step1Chunk8_0_checked, root4Node16Step1Chunk8_1_checked, root4Node16Step1Chunk8_2_checked, root4Node16Step1Chunk8_3_checked, root4Node16Step1Chunk8_4_checked, root4Node16Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node16Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node16Domains1 (.output 6) = true := by decide
def root4Node17Domains0 : Domains 61 State := restrict root4Node15Domains1 52 (6,3)
def root4Node17Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0)]
  | 20 => some [(2,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0)]
  | 29 => some [(3,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root4Node17Domains0_fast_eq : root4Node17Domains0 = expandDomains root4Node17Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node17Domains0 v = expandDomains root4Node17Domains0Fast v from by decide) v
def root4Node17Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(1,0)]
  | 20 => [(2,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(0,0)]
  | 29 => [(3,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(7,3)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(6,4)]
  | 43 => [(4,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(6,3)]
  | 53 => [(7,2)]
  | 54 => [(4,0)]
  | 55 => [(7,3)]
  | 56 => [(4,1)]
  | 57 => [(0,2)]
  | 58 => [(1,1)]
  | 59 => [(5,1)]
  | _ => [(0,1)]
def root4Node17Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0)]
  | 20 => some [(2,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0)]
  | 29 => some [(3,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(6,3)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1)]
  | 57 => some [(0,2)]
  | 58 => some [(1,1)]
  | 59 => some [(5,1)]
  | _ => some [(0,1)]
theorem root4Node17Domains1_fast_eq : root4Node17Domains1 = expandDomains root4Node17Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node17Domains1 v = expandDomains root4Node17Domains1Fast v from by decide) v
theorem root4Node17Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root4Node17Domains0 root4Node17Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node17Domains0 root4Node17Domains1
    root4Node17Domains0Fast root4Node17Domains1Fast
    root4Node17Domains0_fast_eq root4Node17Domains1_fast_eq (by decide)
theorem root4Node17Step1_checked :
    checkReplacement table46 root4Node17Domains0 root4Node17Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node17Step1Chunk0_0_checked, root4Node17Step1Chunk0_1_checked, root4Node17Step1Chunk0_2_checked, root4Node17Step1Chunk0_3_checked, root4Node17Step1Chunk0_4_checked, root4Node17Step1Chunk0_5_checked, root4Node17Step1Chunk1_0_checked, root4Node17Step1Chunk1_1_checked, root4Node17Step1Chunk1_2_checked, root4Node17Step1Chunk1_3_checked, root4Node17Step1Chunk1_4_checked, root4Node17Step1Chunk1_5_checked, root4Node17Step1Chunk2_0_checked, root4Node17Step1Chunk2_1_checked, root4Node17Step1Chunk2_2_checked, root4Node17Step1Chunk2_3_checked, root4Node17Step1Chunk2_4_checked, root4Node17Step1Chunk2_5_checked, root4Node17Step1Chunk3_0_checked, root4Node17Step1Chunk3_1_checked, root4Node17Step1Chunk3_2_checked, root4Node17Step1Chunk3_3_checked, root4Node17Step1Chunk3_4_checked, root4Node17Step1Chunk3_5_checked, root4Node17Step1Chunk4_0_checked, root4Node17Step1Chunk4_1_checked, root4Node17Step1Chunk4_2_checked, root4Node17Step1Chunk4_3_checked, root4Node17Step1Chunk4_4_checked, root4Node17Step1Chunk4_5_checked, root4Node17Step1Chunk5_0_checked, root4Node17Step1Chunk5_1_checked, root4Node17Step1Chunk5_2_checked, root4Node17Step1Chunk5_3_checked, root4Node17Step1Chunk5_4_checked, root4Node17Step1Chunk5_5_checked, root4Node17Step1Chunk6_0_checked, root4Node17Step1Chunk6_1_checked, root4Node17Step1Chunk6_2_checked, root4Node17Step1Chunk6_3_checked, root4Node17Step1Chunk6_4_checked, root4Node17Step1Chunk6_5_checked, root4Node17Step1Chunk7_0_checked, root4Node17Step1Chunk7_1_checked, root4Node17Step1Chunk7_2_checked, root4Node17Step1Chunk7_3_checked, root4Node17Step1Chunk7_4_checked, root4Node17Step1Chunk7_5_checked, root4Node17Step1Chunk8_0_checked, root4Node17Step1Chunk8_1_checked, root4Node17Step1Chunk8_2_checked, root4Node17Step1Chunk8_3_checked, root4Node17Step1Chunk8_4_checked, root4Node17Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node17Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node17Domains1 (.output 7) = true := by decide
def root4Node18Domains0 : Domains 61 State := restrict root4Node14Domains3 34 (8,3)
def root4Node18Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0)]
  | 20 => some [(2,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0)]
  | 29 => some [(3,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4),(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,1),(6,4)]
theorem root4Node18Domains0_fast_eq : root4Node18Domains0 = expandDomains root4Node18Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node18Domains0 v = expandDomains root4Node18Domains0Fast v from by decide) v
def root4Node18Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(1,0)]
  | 20 => [(2,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(0,0)]
  | 29 => [(3,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(8,3)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4)]
  | 43 => [(4,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(8,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3)]
  | 56 => [(4,1),(8,1)]
  | 57 => [(0,2),(6,5)]
  | 58 => [(0,4)]
  | 59 => [(5,4)]
  | _ => [(6,4)]
def root4Node18Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0)]
  | 20 => some [(2,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0)]
  | 29 => some [(3,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(8,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(5,4)]
  | _ => some [(6,4)]
theorem root4Node18Domains1_fast_eq : root4Node18Domains1 = expandDomains root4Node18Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node18Domains1 v = expandDomains root4Node18Domains1Fast v from by decide) v
theorem root4Node18Step1Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root4Node18Domains0 root4Node18Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains0 root4Node18Domains1
    root4Node18Domains0Fast root4Node18Domains1Fast
    root4Node18Domains0_fast_eq root4Node18Domains1_fast_eq (by decide)
theorem root4Node18Step1_checked :
    checkReplacement table40 root4Node18Domains0 root4Node18Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node18Step1Chunk0_0_checked, root4Node18Step1Chunk0_1_checked, root4Node18Step1Chunk0_2_checked, root4Node18Step1Chunk0_3_checked, root4Node18Step1Chunk0_4_checked, root4Node18Step1Chunk0_5_checked, root4Node18Step1Chunk1_0_checked, root4Node18Step1Chunk1_1_checked, root4Node18Step1Chunk1_2_checked, root4Node18Step1Chunk1_3_checked, root4Node18Step1Chunk1_4_checked, root4Node18Step1Chunk1_5_checked, root4Node18Step1Chunk2_0_checked, root4Node18Step1Chunk2_1_checked, root4Node18Step1Chunk2_2_checked, root4Node18Step1Chunk2_3_checked, root4Node18Step1Chunk2_4_checked, root4Node18Step1Chunk2_5_checked, root4Node18Step1Chunk3_0_checked, root4Node18Step1Chunk3_1_checked, root4Node18Step1Chunk3_2_checked, root4Node18Step1Chunk3_3_checked, root4Node18Step1Chunk3_4_checked, root4Node18Step1Chunk3_5_checked, root4Node18Step1Chunk4_0_checked, root4Node18Step1Chunk4_1_checked, root4Node18Step1Chunk4_2_checked, root4Node18Step1Chunk4_3_checked, root4Node18Step1Chunk4_4_checked, root4Node18Step1Chunk4_5_checked, root4Node18Step1Chunk5_0_checked, root4Node18Step1Chunk5_1_checked, root4Node18Step1Chunk5_2_checked, root4Node18Step1Chunk5_3_checked, root4Node18Step1Chunk5_4_checked, root4Node18Step1Chunk5_5_checked, root4Node18Step1Chunk6_0_checked, root4Node18Step1Chunk6_1_checked, root4Node18Step1Chunk6_2_checked, root4Node18Step1Chunk6_3_checked, root4Node18Step1Chunk6_4_checked, root4Node18Step1Chunk6_5_checked, root4Node18Step1Chunk7_0_checked, root4Node18Step1Chunk7_1_checked, root4Node18Step1Chunk7_2_checked, root4Node18Step1Chunk7_3_checked, root4Node18Step1Chunk7_4_checked, root4Node18Step1Chunk7_5_checked, root4Node18Step1Chunk8_0_checked, root4Node18Step1Chunk8_1_checked, root4Node18Step1Chunk8_2_checked, root4Node18Step1Chunk8_3_checked, root4Node18Step1Chunk8_4_checked, root4Node18Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node18Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(1,5)]
  | 4 => [(6,1)]
  | 5 => [(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(8,5)]
  | 9 => [(7,0)]
  | 10 => [(8,3)]
  | 11 => [(0,1)]
  | 12 => [(6,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(7,4)]
  | 17 => [(6,3)]
  | 18 => [(5,5)]
  | 19 => [(1,0)]
  | 20 => [(2,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1)]
  | 24 => [(0,2)]
  | 25 => [(1,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(0,0)]
  | 29 => [(3,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2)]
  | 33 => [(8,0)]
  | 34 => [(8,3)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(1,4)]
  | 43 => [(4,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(7,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(8,2)]
  | 54 => [(8,0)]
  | 55 => [(7,3)]
  | 56 => [(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(5,4)]
  | _ => [(6,4)]
def root4Node18Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(1,5)]
  | 4 => some [(6,1)]
  | 5 => some [(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,1)]
  | 12 => some [(6,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(7,4)]
  | 17 => some [(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0)]
  | 20 => some [(2,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1)]
  | 24 => some [(0,2)]
  | 25 => some [(1,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0)]
  | 29 => some [(3,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2)]
  | 33 => some [(8,0)]
  | 34 => some [(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(1,4)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(8,2)]
  | 54 => some [(8,0)]
  | 55 => some [(7,3)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(5,4)]
  | _ => some [(6,4)]
theorem root4Node18Domains2_fast_eq : root4Node18Domains2 = expandDomains root4Node18Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node18Domains2 v = expandDomains root4Node18Domains2Fast v from by decide) v
theorem root4Node18Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root4Node18Domains1 root4Node18Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node18Domains1 root4Node18Domains2
    root4Node18Domains1Fast root4Node18Domains2Fast
    root4Node18Domains1_fast_eq root4Node18Domains2_fast_eq (by decide)
theorem root4Node18Step2_checked :
    checkReplacement table36 root4Node18Domains1 root4Node18Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node18Step2Chunk0_0_checked, root4Node18Step2Chunk0_1_checked, root4Node18Step2Chunk0_2_checked, root4Node18Step2Chunk0_3_checked, root4Node18Step2Chunk0_4_checked, root4Node18Step2Chunk0_5_checked, root4Node18Step2Chunk1_0_checked, root4Node18Step2Chunk1_1_checked, root4Node18Step2Chunk1_2_checked, root4Node18Step2Chunk1_3_checked, root4Node18Step2Chunk1_4_checked, root4Node18Step2Chunk1_5_checked, root4Node18Step2Chunk2_0_checked, root4Node18Step2Chunk2_1_checked, root4Node18Step2Chunk2_2_checked, root4Node18Step2Chunk2_3_checked, root4Node18Step2Chunk2_4_checked, root4Node18Step2Chunk2_5_checked, root4Node18Step2Chunk3_0_checked, root4Node18Step2Chunk3_1_checked, root4Node18Step2Chunk3_2_checked, root4Node18Step2Chunk3_3_checked, root4Node18Step2Chunk3_4_checked, root4Node18Step2Chunk3_5_checked, root4Node18Step2Chunk4_0_checked, root4Node18Step2Chunk4_1_checked, root4Node18Step2Chunk4_2_checked, root4Node18Step2Chunk4_3_checked, root4Node18Step2Chunk4_4_checked, root4Node18Step2Chunk4_5_checked, root4Node18Step2Chunk5_0_checked, root4Node18Step2Chunk5_1_checked, root4Node18Step2Chunk5_2_checked, root4Node18Step2Chunk5_3_checked, root4Node18Step2Chunk5_4_checked, root4Node18Step2Chunk5_5_checked, root4Node18Step2Chunk6_0_checked, root4Node18Step2Chunk6_1_checked, root4Node18Step2Chunk6_2_checked, root4Node18Step2Chunk6_3_checked, root4Node18Step2Chunk6_4_checked, root4Node18Step2Chunk6_5_checked, root4Node18Step2Chunk7_0_checked, root4Node18Step2Chunk7_1_checked, root4Node18Step2Chunk7_2_checked, root4Node18Step2Chunk7_3_checked, root4Node18Step2Chunk7_4_checked, root4Node18Step2Chunk7_5_checked, root4Node18Step2Chunk8_0_checked, root4Node18Step2Chunk8_1_checked, root4Node18Step2Chunk8_2_checked, root4Node18Step2Chunk8_3_checked, root4Node18Step2Chunk8_4_checked, root4Node18Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node18Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node18Domains2 (.output 8) = true := by decide
def root4Node19Domains0 : Domains 61 State := restrict root4Node1Domains4 3 (6,5)
def root4Node19Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4),(6,1)]
  | 5 => some [(1,3),(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(5,5),(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3),(8,3)]
  | 11 => some [(0,1),(6,5)]
  | 12 => some [(0,4),(6,2)]
  | 13 => some [(1,4),(3,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(4,4),(7,2)]
  | 16 => some [(1,4),(7,4)]
  | 17 => some [(0,5),(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0),(3,0),(7,0)]
  | 20 => some [(2,1),(2,3),(2,5)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0),(6,4)]
  | 29 => some [(1,2),(3,2),(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2),(8,2)]
  | 33 => some [(5,0),(8,0)]
  | 34 => some [(4,5),(7,3),(8,3)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5),(7,5)]
  | 37 => some [(0,3),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0),(1,4),(6,4)]
  | 43 => some [(4,5),(7,3)]
  | 44 => some [(4,2),(7,0)]
  | 45 => some [(5,3),(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(1,2),(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root4Node19Domains0_fast_eq : root4Node19Domains0 = expandDomains root4Node19Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node19Domains0 v = expandDomains root4Node19Domains0Fast v from by decide) v
def root4Node19Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(1,3),(7,3)]
  | 6 => [(4,2)]
  | 7 => [(5,3)]
  | 8 => [(5,5),(8,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,1),(6,5)]
  | 12 => [(0,4),(6,2)]
  | 13 => [(1,4),(3,4),(7,4)]
  | 14 => [(0,5),(6,3)]
  | 15 => [(4,4),(7,2)]
  | 16 => [(1,4),(7,4)]
  | 17 => [(0,5),(6,3)]
  | 18 => [(5,5)]
  | 19 => [(1,0),(3,0),(7,0)]
  | 20 => [(2,1),(2,3),(2,5)]
  | 21 => [(0,2),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(4,1),(7,5)]
  | 24 => [(0,2),(6,0)]
  | 25 => [(1,1),(3,1),(7,1)]
  | 26 => [(0,5)]
  | 27 => [(4,4)]
  | 28 => [(0,0),(6,4)]
  | 29 => [(1,2),(3,2),(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(5,2),(8,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(7,1)]
  | 36 => [(1,5),(7,5)]
  | 37 => [(0,3),(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(4,5),(7,3)]
  | 44 => [(4,2),(7,0)]
  | 45 => [(5,3),(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5)]
  | 50 => [(1,2),(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3),(6,3)]
  | 53 => [(7,2),(8,2)]
  | 54 => [(4,0),(5,0),(8,0)]
  | 55 => [(4,5),(7,3)]
  | 56 => [(4,1),(8,1)]
  | 57 => [(0,2),(6,5)]
  | 58 => [(0,4),(1,1)]
  | 59 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,4)]
def root4Node19Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(1,3),(7,3)]
  | 6 => some [(4,2)]
  | 7 => some [(5,3)]
  | 8 => some [(5,5),(8,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,1),(6,5)]
  | 12 => some [(0,4),(6,2)]
  | 13 => some [(1,4),(3,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(4,4),(7,2)]
  | 16 => some [(1,4),(7,4)]
  | 17 => some [(0,5),(6,3)]
  | 18 => some [(5,5)]
  | 19 => some [(1,0),(3,0),(7,0)]
  | 20 => some [(2,1),(2,3),(2,5)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(4,1),(7,5)]
  | 24 => some [(0,2),(6,0)]
  | 25 => some [(1,1),(3,1),(7,1)]
  | 26 => some [(0,5)]
  | 27 => some [(4,4)]
  | 28 => some [(0,0),(6,4)]
  | 29 => some [(1,2),(3,2),(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(5,2),(8,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5),(7,5)]
  | 37 => some [(0,3),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(4,5),(7,3)]
  | 44 => some [(4,2),(7,0)]
  | 45 => some [(5,3),(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5)]
  | 50 => some [(1,2),(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3),(6,3)]
  | 53 => some [(7,2),(8,2)]
  | 54 => some [(4,0),(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(4,1),(8,1)]
  | 57 => some [(0,2),(6,5)]
  | 58 => some [(0,4),(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root4Node19Domains1_fast_eq : root4Node19Domains1 = expandDomains root4Node19Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node19Domains1 v = expandDomains root4Node19Domains1Fast v from by decide) v
theorem root4Node19Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root4Node19Domains0 root4Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node19Domains0 root4Node19Domains1
    root4Node19Domains0Fast root4Node19Domains1Fast
    root4Node19Domains0_fast_eq root4Node19Domains1_fast_eq (by decide)
theorem root4Node19Step1_checked :
    checkReplacement table23 root4Node19Domains0 root4Node19Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node19Step1Chunk0_0_checked, root4Node19Step1Chunk0_1_checked, root4Node19Step1Chunk0_2_checked, root4Node19Step1Chunk0_3_checked, root4Node19Step1Chunk0_4_checked, root4Node19Step1Chunk0_5_checked, root4Node19Step1Chunk1_0_checked, root4Node19Step1Chunk1_1_checked, root4Node19Step1Chunk1_2_checked, root4Node19Step1Chunk1_3_checked, root4Node19Step1Chunk1_4_checked, root4Node19Step1Chunk1_5_checked, root4Node19Step1Chunk2_0_checked, root4Node19Step1Chunk2_1_checked, root4Node19Step1Chunk2_2_checked, root4Node19Step1Chunk2_3_checked, root4Node19Step1Chunk2_4_checked, root4Node19Step1Chunk2_5_checked, root4Node19Step1Chunk3_0_checked, root4Node19Step1Chunk3_1_checked, root4Node19Step1Chunk3_2_checked, root4Node19Step1Chunk3_3_checked, root4Node19Step1Chunk3_4_checked, root4Node19Step1Chunk3_5_checked, root4Node19Step1Chunk4_0_checked, root4Node19Step1Chunk4_1_checked, root4Node19Step1Chunk4_2_checked, root4Node19Step1Chunk4_3_checked, root4Node19Step1Chunk4_4_checked, root4Node19Step1Chunk4_5_checked, root4Node19Step1Chunk5_0_checked, root4Node19Step1Chunk5_1_checked, root4Node19Step1Chunk5_2_checked, root4Node19Step1Chunk5_3_checked, root4Node19Step1Chunk5_4_checked, root4Node19Step1Chunk5_5_checked, root4Node19Step1Chunk6_0_checked, root4Node19Step1Chunk6_1_checked, root4Node19Step1Chunk6_2_checked, root4Node19Step1Chunk6_3_checked, root4Node19Step1Chunk6_4_checked, root4Node19Step1Chunk6_5_checked, root4Node19Step1Chunk7_0_checked, root4Node19Step1Chunk7_1_checked, root4Node19Step1Chunk7_2_checked, root4Node19Step1Chunk7_3_checked, root4Node19Step1Chunk7_4_checked, root4Node19Step1Chunk7_5_checked, root4Node19Step1Chunk8_0_checked, root4Node19Step1Chunk8_1_checked, root4Node19Step1Chunk8_2_checked, root4Node19Step1Chunk8_3_checked, root4Node19Step1Chunk8_4_checked, root4Node19Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
