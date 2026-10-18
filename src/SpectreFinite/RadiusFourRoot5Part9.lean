module

public import SpectreFinite.RadiusFourRoot5Part8
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
def root5Node24Domains0 : Domains 61 State := restrict root5Node23Domains2 52 (5,5)
def root5Node24Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(1,5)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(3,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node24Domains0_fast_eq : root5Node24Domains0 = expandDomains root5Node24Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node24Domains0 v = expandDomains root5Node24Domains0Fast v from by decide) v
def root5Node24Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0)]
  | 4 => [(7,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(1,5)]
  | 9 => [(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(3,1)]
  | 23 => [(0,1)]
  | 24 => [(6,2)]
  | 25 => [(8,4)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(5,4)]
  | 36 => [(6,4)]
  | 37 => [(1,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(0,3)]
  | 45 => [(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(4,2)]
  | 51 => [(5,3)]
  | 52 => [(5,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5)]
  | 56 => [(1,4)]
  | 57 => [(0,5)]
  | 58 => [(4,4)]
  | 59 => [(1,4)]
  | _ => [(0,5)]
def root5Node24Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(1,5)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(3,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(5,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5)]
  | 56 => some [(1,4)]
  | 57 => some [(0,5)]
  | 58 => some [(4,4)]
  | 59 => some [(1,4)]
  | _ => some [(0,5)]
theorem root5Node24Domains1_fast_eq : root5Node24Domains1 = expandDomains root5Node24Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node24Domains1 v = expandDomains root5Node24Domains1Fast v from by decide) v
theorem root5Node24Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root5Node24Domains0 root5Node24Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node24Domains0 root5Node24Domains1
    root5Node24Domains0Fast root5Node24Domains1Fast
    root5Node24Domains0_fast_eq root5Node24Domains1_fast_eq (by decide)
theorem root5Node24Step1_checked :
    checkReplacement table46 root5Node24Domains0 root5Node24Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node24Step1Chunk0_0_checked, root5Node24Step1Chunk0_1_checked, root5Node24Step1Chunk0_2_checked, root5Node24Step1Chunk0_3_checked, root5Node24Step1Chunk0_4_checked, root5Node24Step1Chunk0_5_checked, root5Node24Step1Chunk1_0_checked, root5Node24Step1Chunk1_1_checked, root5Node24Step1Chunk1_2_checked, root5Node24Step1Chunk1_3_checked, root5Node24Step1Chunk1_4_checked, root5Node24Step1Chunk1_5_checked, root5Node24Step1Chunk2_0_checked, root5Node24Step1Chunk2_1_checked, root5Node24Step1Chunk2_2_checked, root5Node24Step1Chunk2_3_checked, root5Node24Step1Chunk2_4_checked, root5Node24Step1Chunk2_5_checked, root5Node24Step1Chunk3_0_checked, root5Node24Step1Chunk3_1_checked, root5Node24Step1Chunk3_2_checked, root5Node24Step1Chunk3_3_checked, root5Node24Step1Chunk3_4_checked, root5Node24Step1Chunk3_5_checked, root5Node24Step1Chunk4_0_checked, root5Node24Step1Chunk4_1_checked, root5Node24Step1Chunk4_2_checked, root5Node24Step1Chunk4_3_checked, root5Node24Step1Chunk4_4_checked, root5Node24Step1Chunk4_5_checked, root5Node24Step1Chunk5_0_checked, root5Node24Step1Chunk5_1_checked, root5Node24Step1Chunk5_2_checked, root5Node24Step1Chunk5_3_checked, root5Node24Step1Chunk5_4_checked, root5Node24Step1Chunk5_5_checked, root5Node24Step1Chunk6_0_checked, root5Node24Step1Chunk6_1_checked, root5Node24Step1Chunk6_2_checked, root5Node24Step1Chunk6_3_checked, root5Node24Step1Chunk6_4_checked, root5Node24Step1Chunk6_5_checked, root5Node24Step1Chunk7_0_checked, root5Node24Step1Chunk7_1_checked, root5Node24Step1Chunk7_2_checked, root5Node24Step1Chunk7_3_checked, root5Node24Step1Chunk7_4_checked, root5Node24Step1Chunk7_5_checked, root5Node24Step1Chunk8_0_checked, root5Node24Step1Chunk8_1_checked, root5Node24Step1Chunk8_2_checked, root5Node24Step1Chunk8_3_checked, root5Node24Step1Chunk8_4_checked, root5Node24Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node24Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node24Domains1 (.output 10) = true := by decide
def root5Node25Domains0 : Domains 61 State := restrict root5Node23Domains2 52 (8,5)
def root5Node25Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(1,5)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(3,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node25Domains0_fast_eq : root5Node25Domains0 = expandDomains root5Node25Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node25Domains0 v = expandDomains root5Node25Domains0Fast v from by decide) v
def root5Node25Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0)]
  | 4 => [(7,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(1,5)]
  | 9 => [(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(3,1)]
  | 23 => [(0,1)]
  | 24 => [(6,2)]
  | 25 => [(8,4)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(5,4)]
  | 36 => [(6,4)]
  | 37 => [(1,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(0,3)]
  | 45 => [(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(4,2)]
  | 51 => [(5,3)]
  | 52 => [(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(3,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root5Node25Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(1,5)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(3,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(3,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root5Node25Domains1_fast_eq : root5Node25Domains1 = expandDomains root5Node25Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node25Domains1 v = expandDomains root5Node25Domains1Fast v from by decide) v
theorem root5Node25Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root5Node25Domains0 root5Node25Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node25Domains0 root5Node25Domains1
    root5Node25Domains0Fast root5Node25Domains1Fast
    root5Node25Domains0_fast_eq root5Node25Domains1_fast_eq (by decide)
theorem root5Node25Step1_checked :
    checkReplacement table46 root5Node25Domains0 root5Node25Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node25Step1Chunk0_0_checked, root5Node25Step1Chunk0_1_checked, root5Node25Step1Chunk0_2_checked, root5Node25Step1Chunk0_3_checked, root5Node25Step1Chunk0_4_checked, root5Node25Step1Chunk0_5_checked, root5Node25Step1Chunk1_0_checked, root5Node25Step1Chunk1_1_checked, root5Node25Step1Chunk1_2_checked, root5Node25Step1Chunk1_3_checked, root5Node25Step1Chunk1_4_checked, root5Node25Step1Chunk1_5_checked, root5Node25Step1Chunk2_0_checked, root5Node25Step1Chunk2_1_checked, root5Node25Step1Chunk2_2_checked, root5Node25Step1Chunk2_3_checked, root5Node25Step1Chunk2_4_checked, root5Node25Step1Chunk2_5_checked, root5Node25Step1Chunk3_0_checked, root5Node25Step1Chunk3_1_checked, root5Node25Step1Chunk3_2_checked, root5Node25Step1Chunk3_3_checked, root5Node25Step1Chunk3_4_checked, root5Node25Step1Chunk3_5_checked, root5Node25Step1Chunk4_0_checked, root5Node25Step1Chunk4_1_checked, root5Node25Step1Chunk4_2_checked, root5Node25Step1Chunk4_3_checked, root5Node25Step1Chunk4_4_checked, root5Node25Step1Chunk4_5_checked, root5Node25Step1Chunk5_0_checked, root5Node25Step1Chunk5_1_checked, root5Node25Step1Chunk5_2_checked, root5Node25Step1Chunk5_3_checked, root5Node25Step1Chunk5_4_checked, root5Node25Step1Chunk5_5_checked, root5Node25Step1Chunk6_0_checked, root5Node25Step1Chunk6_1_checked, root5Node25Step1Chunk6_2_checked, root5Node25Step1Chunk6_3_checked, root5Node25Step1Chunk6_4_checked, root5Node25Step1Chunk6_5_checked, root5Node25Step1Chunk7_0_checked, root5Node25Step1Chunk7_1_checked, root5Node25Step1Chunk7_2_checked, root5Node25Step1Chunk7_3_checked, root5Node25Step1Chunk7_4_checked, root5Node25Step1Chunk7_5_checked, root5Node25Step1Chunk8_0_checked, root5Node25Step1Chunk8_1_checked, root5Node25Step1Chunk8_2_checked, root5Node25Step1Chunk8_3_checked, root5Node25Step1Chunk8_4_checked, root5Node25Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node25Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node25Domains1 (.output 11) = true := by decide
def root5Node26Domains0 : Domains 61 State := restrict root5Node22Domains1 35 (8,4)
def root5Node26Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(1,5)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(3,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(8,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(7,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root5Node26Domains0_fast_eq : root5Node26Domains0 = expandDomains root5Node26Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node26Domains0 v = expandDomains root5Node26Domains0Fast v from by decide) v
def root5Node26Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0)]
  | 4 => [(7,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(1,5)]
  | 9 => [(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(3,1)]
  | 23 => [(0,1)]
  | 24 => [(6,2)]
  | 25 => [(8,4)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(8,4)]
  | 36 => [(6,4)]
  | 37 => [(1,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(0,3)]
  | 45 => [(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(4,2)]
  | 51 => [(5,3)]
  | 52 => [(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root5Node26Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(1,5)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(3,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(8,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root5Node26Domains1_fast_eq : root5Node26Domains1 = expandDomains root5Node26Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node26Domains1 v = expandDomains root5Node26Domains1Fast v from by decide) v
theorem root5Node26Step1Chunk0_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk0_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk0_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk0_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk0_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk0_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk1_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk2_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk3_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk4_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk5_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk6_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk7_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_0⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_1⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_2⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_3⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_4⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1Chunk8_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_5⟩
      root5Node26Domains0 root5Node26Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains0 root5Node26Domains1
    root5Node26Domains0Fast root5Node26Domains1Fast
    root5Node26Domains0_fast_eq root5Node26Domains1_fast_eq (by decide)
theorem root5Node26Step1_checked :
    checkReplacement table38 root5Node26Domains0 root5Node26Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node26Step1Chunk0_0_checked, root5Node26Step1Chunk0_1_checked, root5Node26Step1Chunk0_2_checked, root5Node26Step1Chunk0_3_checked, root5Node26Step1Chunk0_4_checked, root5Node26Step1Chunk0_5_checked, root5Node26Step1Chunk1_0_checked, root5Node26Step1Chunk1_1_checked, root5Node26Step1Chunk1_2_checked, root5Node26Step1Chunk1_3_checked, root5Node26Step1Chunk1_4_checked, root5Node26Step1Chunk1_5_checked, root5Node26Step1Chunk2_0_checked, root5Node26Step1Chunk2_1_checked, root5Node26Step1Chunk2_2_checked, root5Node26Step1Chunk2_3_checked, root5Node26Step1Chunk2_4_checked, root5Node26Step1Chunk2_5_checked, root5Node26Step1Chunk3_0_checked, root5Node26Step1Chunk3_1_checked, root5Node26Step1Chunk3_2_checked, root5Node26Step1Chunk3_3_checked, root5Node26Step1Chunk3_4_checked, root5Node26Step1Chunk3_5_checked, root5Node26Step1Chunk4_0_checked, root5Node26Step1Chunk4_1_checked, root5Node26Step1Chunk4_2_checked, root5Node26Step1Chunk4_3_checked, root5Node26Step1Chunk4_4_checked, root5Node26Step1Chunk4_5_checked, root5Node26Step1Chunk5_0_checked, root5Node26Step1Chunk5_1_checked, root5Node26Step1Chunk5_2_checked, root5Node26Step1Chunk5_3_checked, root5Node26Step1Chunk5_4_checked, root5Node26Step1Chunk5_5_checked, root5Node26Step1Chunk6_0_checked, root5Node26Step1Chunk6_1_checked, root5Node26Step1Chunk6_2_checked, root5Node26Step1Chunk6_3_checked, root5Node26Step1Chunk6_4_checked, root5Node26Step1Chunk6_5_checked, root5Node26Step1Chunk7_0_checked, root5Node26Step1Chunk7_1_checked, root5Node26Step1Chunk7_2_checked, root5Node26Step1Chunk7_3_checked, root5Node26Step1Chunk7_4_checked, root5Node26Step1Chunk7_5_checked, root5Node26Step1Chunk8_0_checked, root5Node26Step1Chunk8_1_checked, root5Node26Step1Chunk8_2_checked, root5Node26Step1Chunk8_3_checked, root5Node26Step1Chunk8_4_checked, root5Node26Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node26Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0)]
  | 4 => [(7,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(1,5)]
  | 9 => [(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(3,1)]
  | 23 => [(0,1)]
  | 24 => [(6,2)]
  | 25 => [(8,4)]
  | 26 => [(8,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(8,4)]
  | 36 => [(6,4)]
  | 37 => [(1,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5)]
  | 44 => [(0,3)]
  | 45 => [(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(4,2)]
  | 51 => [(5,3)]
  | 52 => [(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(7,4)]
  | 57 => [(6,3)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(1,3),(6,3)]
def root5Node26Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(1,5)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(3,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(8,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3),(6,3)]
theorem root5Node26Domains2_fast_eq : root5Node26Domains2 = expandDomains root5Node26Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node26Domains2 v = expandDomains root5Node26Domains2Fast v from by decide) v
theorem root5Node26Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root5Node26Domains1 root5Node26Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node26Domains1 root5Node26Domains2
    root5Node26Domains1Fast root5Node26Domains2Fast
    root5Node26Domains1_fast_eq root5Node26Domains2_fast_eq (by decide)
theorem root5Node26Step2_checked :
    checkReplacement table39 root5Node26Domains1 root5Node26Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node26Step2Chunk0_0_checked, root5Node26Step2Chunk0_1_checked, root5Node26Step2Chunk0_2_checked, root5Node26Step2Chunk0_3_checked, root5Node26Step2Chunk0_4_checked, root5Node26Step2Chunk0_5_checked, root5Node26Step2Chunk1_0_checked, root5Node26Step2Chunk1_1_checked, root5Node26Step2Chunk1_2_checked, root5Node26Step2Chunk1_3_checked, root5Node26Step2Chunk1_4_checked, root5Node26Step2Chunk1_5_checked, root5Node26Step2Chunk2_0_checked, root5Node26Step2Chunk2_1_checked, root5Node26Step2Chunk2_2_checked, root5Node26Step2Chunk2_3_checked, root5Node26Step2Chunk2_4_checked, root5Node26Step2Chunk2_5_checked, root5Node26Step2Chunk3_0_checked, root5Node26Step2Chunk3_1_checked, root5Node26Step2Chunk3_2_checked, root5Node26Step2Chunk3_3_checked, root5Node26Step2Chunk3_4_checked, root5Node26Step2Chunk3_5_checked, root5Node26Step2Chunk4_0_checked, root5Node26Step2Chunk4_1_checked, root5Node26Step2Chunk4_2_checked, root5Node26Step2Chunk4_3_checked, root5Node26Step2Chunk4_4_checked, root5Node26Step2Chunk4_5_checked, root5Node26Step2Chunk5_0_checked, root5Node26Step2Chunk5_1_checked, root5Node26Step2Chunk5_2_checked, root5Node26Step2Chunk5_3_checked, root5Node26Step2Chunk5_4_checked, root5Node26Step2Chunk5_5_checked, root5Node26Step2Chunk6_0_checked, root5Node26Step2Chunk6_1_checked, root5Node26Step2Chunk6_2_checked, root5Node26Step2Chunk6_3_checked, root5Node26Step2Chunk6_4_checked, root5Node26Step2Chunk6_5_checked, root5Node26Step2Chunk7_0_checked, root5Node26Step2Chunk7_1_checked, root5Node26Step2Chunk7_2_checked, root5Node26Step2Chunk7_3_checked, root5Node26Step2Chunk7_4_checked, root5Node26Step2Chunk7_5_checked, root5Node26Step2Chunk8_0_checked, root5Node26Step2Chunk8_1_checked, root5Node26Step2Chunk8_2_checked, root5Node26Step2Chunk8_3_checked, root5Node26Step2Chunk8_4_checked, root5Node26Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node27Domains0 : Domains 61 State := restrict root5Node26Domains2 60 (1,3)
def root5Node27Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(1,5)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(3,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(8,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(8,4)]
  | 36 => some [(6,4)]
  | 37 => some [(1,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5)]
  | 44 => some [(0,3)]
  | 45 => some [(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(4,2)]
  | 51 => some [(5,3)]
  | 52 => some [(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(7,4)]
  | 57 => some [(6,3)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(1,3)]
theorem root5Node27Domains0_fast_eq : root5Node27Domains0 = expandDomains root5Node27Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node27Domains0 v = expandDomains root5Node27Domains0Fast v from by decide) v
theorem root5Node27Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node27Domains0 (.output 12) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
