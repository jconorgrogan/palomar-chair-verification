module

public import SpectreFinite.RadiusFourRoot5Part9
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable2
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node28Domains0 : Domains 61 State := restrict root5Node26Domains2 60 (6,3)
def root5Node28Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | _ => some [(6,3)]
theorem root5Node28Domains0_fast_eq : root5Node28Domains0 = expandDomains root5Node28Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node28Domains0 v = expandDomains root5Node28Domains0Fast v from by decide) v
theorem root5Node28Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node28Domains0 (.output 13) = true := by decide
def root5Node29Domains0 : Domains 61 State := restrict root5Node19Domains2 3 (6,4)
def root5Node29Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2),(7,2)]
  | 5 => some [(5,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(1,5),(3,5),(7,5)]
  | 9 => some [(0,3),(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5),(6,3)]
  | 12 => some [(4,4),(7,2)]
  | 13 => some [(1,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4)]
  | 16 => some [(1,3),(3,3),(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2),(6,0)]
  | 19 => some [(1,1),(7,1)]
  | 20 => some [(4,1),(7,5)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(3,1),(7,1)]
  | 23 => some [(0,1),(6,5)]
  | 24 => some [(0,4),(6,2)]
  | 25 => some [(5,4),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(7,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1),(8,1)]
  | 49 => some [(0,1),(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root5Node29Domains0_fast_eq : root5Node29Domains0 = expandDomains root5Node29Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node29Domains0 v = expandDomains root5Node29Domains0Fast v from by decide) v
def root5Node29Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(5,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(3,5),(7,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,5),(6,3)]
  | 12 => [(4,4),(7,2)]
  | 13 => [(1,4),(7,4)]
  | 14 => [(0,5),(6,3)]
  | 15 => [(2,2),(2,4)]
  | 16 => [(1,3),(3,3)]
  | 17 => [(5,2)]
  | 18 => [(0,2),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(0,2),(6,0)]
  | 22 => [(1,1),(7,1)]
  | 23 => [(0,1),(6,5)]
  | 24 => [(0,4),(6,2)]
  | 25 => [(5,4),(8,4)]
  | 26 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0),(7,0)]
  | 33 => [(4,3),(7,1)]
  | 34 => [(7,5)]
  | 35 => [(5,1),(5,4),(8,4)]
  | 36 => [(0,1),(6,4)]
  | 37 => [(1,2),(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0),(7,4)]
  | 42 => [(1,3),(7,3)]
  | 43 => [(7,5),(8,5)]
  | 44 => [(0,3),(1,0)]
  | 45 => [(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1),(8,1)]
  | 49 => [(0,1),(6,5)]
  | 50 => [(4,2),(8,2)]
  | 51 => [(5,0),(5,3)]
  | 52 => [(4,5),(5,5),(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(1,4),(3,4),(5,4),(7,4)]
  | 57 => [(0,0),(0,5),(6,3)]
  | 58 => [(4,4),(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root5Node29Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5),(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5),(6,3)]
  | 12 => some [(4,4),(7,2)]
  | 13 => some [(1,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(2,2),(2,4)]
  | 16 => some [(1,3),(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2),(6,0)]
  | 19 => some [(1,1),(7,1)]
  | 20 => some [(4,1),(7,5)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(0,1),(6,5)]
  | 24 => some [(0,4),(6,2)]
  | 25 => some [(5,4),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(7,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1),(8,1)]
  | 49 => some [(0,1),(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root5Node29Domains1_fast_eq : root5Node29Domains1 = expandDomains root5Node29Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node29Domains1 v = expandDomains root5Node29Domains1Fast v from by decide) v
theorem root5Node29Step1Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root5Node29Domains0 root5Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node29Domains0 root5Node29Domains1
    root5Node29Domains0Fast root5Node29Domains1Fast
    root5Node29Domains0_fast_eq root5Node29Domains1_fast_eq (by decide)
theorem root5Node29Step1_checked :
    checkReplacement table2 root5Node29Domains0 root5Node29Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node29Step1Chunk0_0_checked, root5Node29Step1Chunk0_1_checked, root5Node29Step1Chunk0_2_checked, root5Node29Step1Chunk0_3_checked, root5Node29Step1Chunk0_4_checked, root5Node29Step1Chunk0_5_checked, root5Node29Step1Chunk1_0_checked, root5Node29Step1Chunk1_1_checked, root5Node29Step1Chunk1_2_checked, root5Node29Step1Chunk1_3_checked, root5Node29Step1Chunk1_4_checked, root5Node29Step1Chunk1_5_checked, root5Node29Step1Chunk2_0_checked, root5Node29Step1Chunk2_1_checked, root5Node29Step1Chunk2_2_checked, root5Node29Step1Chunk2_3_checked, root5Node29Step1Chunk2_4_checked, root5Node29Step1Chunk2_5_checked, root5Node29Step1Chunk3_0_checked, root5Node29Step1Chunk3_1_checked, root5Node29Step1Chunk3_2_checked, root5Node29Step1Chunk3_3_checked, root5Node29Step1Chunk3_4_checked, root5Node29Step1Chunk3_5_checked, root5Node29Step1Chunk4_0_checked, root5Node29Step1Chunk4_1_checked, root5Node29Step1Chunk4_2_checked, root5Node29Step1Chunk4_3_checked, root5Node29Step1Chunk4_4_checked, root5Node29Step1Chunk4_5_checked, root5Node29Step1Chunk5_0_checked, root5Node29Step1Chunk5_1_checked, root5Node29Step1Chunk5_2_checked, root5Node29Step1Chunk5_3_checked, root5Node29Step1Chunk5_4_checked, root5Node29Step1Chunk5_5_checked, root5Node29Step1Chunk6_0_checked, root5Node29Step1Chunk6_1_checked, root5Node29Step1Chunk6_2_checked, root5Node29Step1Chunk6_3_checked, root5Node29Step1Chunk6_4_checked, root5Node29Step1Chunk6_5_checked, root5Node29Step1Chunk7_0_checked, root5Node29Step1Chunk7_1_checked, root5Node29Step1Chunk7_2_checked, root5Node29Step1Chunk7_3_checked, root5Node29Step1Chunk7_4_checked, root5Node29Step1Chunk7_5_checked, root5Node29Step1Chunk8_0_checked, root5Node29Step1Chunk8_1_checked, root5Node29Step1Chunk8_2_checked, root5Node29Step1Chunk8_3_checked, root5Node29Step1Chunk8_4_checked, root5Node29Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node30Domains0 : Domains 61 State := restrict root5Node29Domains1 5 (5,5)
def root5Node30Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5),(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5),(6,3)]
  | 12 => some [(4,4),(7,2)]
  | 13 => some [(1,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(2,2),(2,4)]
  | 16 => some [(1,3),(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2),(6,0)]
  | 19 => some [(1,1),(7,1)]
  | 20 => some [(4,1),(7,5)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(7,1)]
  | 23 => some [(0,1),(6,5)]
  | 24 => some [(0,4),(6,2)]
  | 25 => some [(5,4),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(7,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1),(8,1)]
  | 49 => some [(0,1),(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root5Node30Domains0_fast_eq : root5Node30Domains0 = expandDomains root5Node30Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node30Domains0 v = expandDomains root5Node30Domains0Fast v from by decide) v
def root5Node30Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(3,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,4)]
  | 16 => [(1,3),(3,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(6,5)]
  | 24 => [(0,4),(6,2)]
  | 25 => [(5,4),(8,4)]
  | 26 => [(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3),(7,1)]
  | 34 => [(7,5)]
  | 35 => [(5,1),(5,4),(8,4)]
  | 36 => [(0,1),(6,4)]
  | 37 => [(1,2),(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0),(7,4)]
  | 42 => [(1,3),(7,3)]
  | 43 => [(7,5),(8,5)]
  | 44 => [(0,3),(1,0)]
  | 45 => [(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1),(8,1)]
  | 49 => [(0,1),(6,5)]
  | 50 => [(4,2),(8,2)]
  | 51 => [(5,0),(5,3)]
  | 52 => [(4,5),(5,5),(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(1,4),(3,4),(5,4),(7,4)]
  | 57 => [(0,0),(0,5),(6,3)]
  | 58 => [(4,4),(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root5Node30Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3),(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4),(6,2)]
  | 25 => some [(5,4),(8,4)]
  | 26 => some [(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3),(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(7,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1),(8,1)]
  | 49 => some [(0,1),(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root5Node30Domains1_fast_eq : root5Node30Domains1 = expandDomains root5Node30Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node30Domains1 v = expandDomains root5Node30Domains1Fast v from by decide) v
theorem root5Node30Step1Chunk0_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_0⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk0_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_1⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk0_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_2⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk0_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_3⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk0_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_4⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk0_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_5⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk1_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_0⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk1_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_1⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk1_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_2⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk1_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_3⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk1_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_4⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk1_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_5⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk2_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_0⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk2_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_1⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk2_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_2⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk2_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_3⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk2_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_4⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk2_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_5⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk3_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_0⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk3_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_1⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk3_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_2⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk3_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_3⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk3_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_4⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk3_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_5⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk4_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_0⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk4_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_1⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk4_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_2⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk4_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_3⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk4_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_4⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk4_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_5⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk5_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_0⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk5_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_1⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk5_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_2⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk5_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_3⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk5_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_4⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk5_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_5⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk6_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_0⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk6_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_1⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk6_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_2⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk6_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_3⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk6_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_4⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk6_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_5⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk7_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_0⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk7_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_1⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk7_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_2⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk7_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_3⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk7_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_4⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk7_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_5⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk8_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_0⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk8_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_1⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk8_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_2⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk8_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_3⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk8_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_4⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1Chunk8_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_5⟩
      root5Node30Domains0 root5Node30Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains0 root5Node30Domains1
    root5Node30Domains0Fast root5Node30Domains1Fast
    root5Node30Domains0_fast_eq root5Node30Domains1_fast_eq (by decide)
theorem root5Node30Step1_checked :
    checkReplacement table29 root5Node30Domains0 root5Node30Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node30Step1Chunk0_0_checked, root5Node30Step1Chunk0_1_checked, root5Node30Step1Chunk0_2_checked, root5Node30Step1Chunk0_3_checked, root5Node30Step1Chunk0_4_checked, root5Node30Step1Chunk0_5_checked, root5Node30Step1Chunk1_0_checked, root5Node30Step1Chunk1_1_checked, root5Node30Step1Chunk1_2_checked, root5Node30Step1Chunk1_3_checked, root5Node30Step1Chunk1_4_checked, root5Node30Step1Chunk1_5_checked, root5Node30Step1Chunk2_0_checked, root5Node30Step1Chunk2_1_checked, root5Node30Step1Chunk2_2_checked, root5Node30Step1Chunk2_3_checked, root5Node30Step1Chunk2_4_checked, root5Node30Step1Chunk2_5_checked, root5Node30Step1Chunk3_0_checked, root5Node30Step1Chunk3_1_checked, root5Node30Step1Chunk3_2_checked, root5Node30Step1Chunk3_3_checked, root5Node30Step1Chunk3_4_checked, root5Node30Step1Chunk3_5_checked, root5Node30Step1Chunk4_0_checked, root5Node30Step1Chunk4_1_checked, root5Node30Step1Chunk4_2_checked, root5Node30Step1Chunk4_3_checked, root5Node30Step1Chunk4_4_checked, root5Node30Step1Chunk4_5_checked, root5Node30Step1Chunk5_0_checked, root5Node30Step1Chunk5_1_checked, root5Node30Step1Chunk5_2_checked, root5Node30Step1Chunk5_3_checked, root5Node30Step1Chunk5_4_checked, root5Node30Step1Chunk5_5_checked, root5Node30Step1Chunk6_0_checked, root5Node30Step1Chunk6_1_checked, root5Node30Step1Chunk6_2_checked, root5Node30Step1Chunk6_3_checked, root5Node30Step1Chunk6_4_checked, root5Node30Step1Chunk6_5_checked, root5Node30Step1Chunk7_0_checked, root5Node30Step1Chunk7_1_checked, root5Node30Step1Chunk7_2_checked, root5Node30Step1Chunk7_3_checked, root5Node30Step1Chunk7_4_checked, root5Node30Step1Chunk7_5_checked, root5Node30Step1Chunk8_0_checked, root5Node30Step1Chunk8_1_checked, root5Node30Step1Chunk8_2_checked, root5Node30Step1Chunk8_3_checked, root5Node30Step1Chunk8_4_checked, root5Node30Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node30Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(3,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,4)]
  | 16 => [(1,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(6,5)]
  | 24 => [(0,4)]
  | 25 => [(5,4)]
  | 26 => [(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(7,5)]
  | 35 => [(5,1),(5,4),(8,4)]
  | 36 => [(0,1),(6,4)]
  | 37 => [(1,2),(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(7,5),(8,5)]
  | 44 => [(0,3),(1,0)]
  | 45 => [(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(4,2),(8,2)]
  | 51 => [(5,0),(5,3)]
  | 52 => [(4,5),(5,5),(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(1,4),(3,4),(5,4),(7,4)]
  | 57 => [(0,0),(0,5),(6,3)]
  | 58 => [(4,4),(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root5Node30Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node30Domains2_fast_eq : root5Node30Domains2 = expandDomains root5Node30Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node30Domains2 v = expandDomains root5Node30Domains2Fast v from by decide) v
theorem root5Node30Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root5Node30Domains1 root5Node30Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node30Domains1 root5Node30Domains2
    root5Node30Domains1Fast root5Node30Domains2Fast
    root5Node30Domains1_fast_eq root5Node30Domains2_fast_eq (by decide)
theorem root5Node30Step2_checked :
    checkReplacement table40 root5Node30Domains1 root5Node30Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node30Step2Chunk0_0_checked, root5Node30Step2Chunk0_1_checked, root5Node30Step2Chunk0_2_checked, root5Node30Step2Chunk0_3_checked, root5Node30Step2Chunk0_4_checked, root5Node30Step2Chunk0_5_checked, root5Node30Step2Chunk1_0_checked, root5Node30Step2Chunk1_1_checked, root5Node30Step2Chunk1_2_checked, root5Node30Step2Chunk1_3_checked, root5Node30Step2Chunk1_4_checked, root5Node30Step2Chunk1_5_checked, root5Node30Step2Chunk2_0_checked, root5Node30Step2Chunk2_1_checked, root5Node30Step2Chunk2_2_checked, root5Node30Step2Chunk2_3_checked, root5Node30Step2Chunk2_4_checked, root5Node30Step2Chunk2_5_checked, root5Node30Step2Chunk3_0_checked, root5Node30Step2Chunk3_1_checked, root5Node30Step2Chunk3_2_checked, root5Node30Step2Chunk3_3_checked, root5Node30Step2Chunk3_4_checked, root5Node30Step2Chunk3_5_checked, root5Node30Step2Chunk4_0_checked, root5Node30Step2Chunk4_1_checked, root5Node30Step2Chunk4_2_checked, root5Node30Step2Chunk4_3_checked, root5Node30Step2Chunk4_4_checked, root5Node30Step2Chunk4_5_checked, root5Node30Step2Chunk5_0_checked, root5Node30Step2Chunk5_1_checked, root5Node30Step2Chunk5_2_checked, root5Node30Step2Chunk5_3_checked, root5Node30Step2Chunk5_4_checked, root5Node30Step2Chunk5_5_checked, root5Node30Step2Chunk6_0_checked, root5Node30Step2Chunk6_1_checked, root5Node30Step2Chunk6_2_checked, root5Node30Step2Chunk6_3_checked, root5Node30Step2Chunk6_4_checked, root5Node30Step2Chunk6_5_checked, root5Node30Step2Chunk7_0_checked, root5Node30Step2Chunk7_1_checked, root5Node30Step2Chunk7_2_checked, root5Node30Step2Chunk7_3_checked, root5Node30Step2Chunk7_4_checked, root5Node30Step2Chunk7_5_checked, root5Node30Step2Chunk8_0_checked, root5Node30Step2Chunk8_1_checked, root5Node30Step2Chunk8_2_checked, root5Node30Step2Chunk8_3_checked, root5Node30Step2Chunk8_4_checked, root5Node30Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node31Domains0 : Domains 61 State := restrict root5Node30Domains2 26 (7,2)
def root5Node31Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(4,2),(8,2)]
  | 51 => some [(5,0),(5,3)]
  | 52 => some [(4,5),(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(5,4),(7,4)]
  | 57 => some [(0,0),(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node31Domains0_fast_eq : root5Node31Domains0 = expandDomains root5Node31Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node31Domains0 v = expandDomains root5Node31Domains0Fast v from by decide) v
def root5Node31Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(3,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,4)]
  | 16 => [(1,3)]
  | 17 => [(5,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(6,5)]
  | 24 => [(0,4)]
  | 25 => [(5,4)]
  | 26 => [(7,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3)]
  | 34 => [(7,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(7,4)]
  | 42 => [(1,3)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(8,1)]
  | 49 => [(6,5)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(5,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root5Node31Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(3,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,4)]
  | 16 => some [(1,3)]
  | 17 => some [(5,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(6,5)]
  | 24 => some [(0,4)]
  | 25 => some [(5,4)]
  | 26 => some [(7,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(7,4)]
  | 42 => some [(1,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(8,1)]
  | 49 => some [(6,5)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(5,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node31Domains1_fast_eq : root5Node31Domains1 = expandDomains root5Node31Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node31Domains1 v = expandDomains root5Node31Domains1Fast v from by decide) v
theorem root5Node31Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root5Node31Domains0 root5Node31Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node31Domains0 root5Node31Domains1
    root5Node31Domains0Fast root5Node31Domains1Fast
    root5Node31Domains0_fast_eq root5Node31Domains1_fast_eq (by decide)
theorem root5Node31Step1_checked :
    checkReplacement table37 root5Node31Domains0 root5Node31Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node31Step1Chunk0_0_checked, root5Node31Step1Chunk0_1_checked, root5Node31Step1Chunk0_2_checked, root5Node31Step1Chunk0_3_checked, root5Node31Step1Chunk0_4_checked, root5Node31Step1Chunk0_5_checked, root5Node31Step1Chunk1_0_checked, root5Node31Step1Chunk1_1_checked, root5Node31Step1Chunk1_2_checked, root5Node31Step1Chunk1_3_checked, root5Node31Step1Chunk1_4_checked, root5Node31Step1Chunk1_5_checked, root5Node31Step1Chunk2_0_checked, root5Node31Step1Chunk2_1_checked, root5Node31Step1Chunk2_2_checked, root5Node31Step1Chunk2_3_checked, root5Node31Step1Chunk2_4_checked, root5Node31Step1Chunk2_5_checked, root5Node31Step1Chunk3_0_checked, root5Node31Step1Chunk3_1_checked, root5Node31Step1Chunk3_2_checked, root5Node31Step1Chunk3_3_checked, root5Node31Step1Chunk3_4_checked, root5Node31Step1Chunk3_5_checked, root5Node31Step1Chunk4_0_checked, root5Node31Step1Chunk4_1_checked, root5Node31Step1Chunk4_2_checked, root5Node31Step1Chunk4_3_checked, root5Node31Step1Chunk4_4_checked, root5Node31Step1Chunk4_5_checked, root5Node31Step1Chunk5_0_checked, root5Node31Step1Chunk5_1_checked, root5Node31Step1Chunk5_2_checked, root5Node31Step1Chunk5_3_checked, root5Node31Step1Chunk5_4_checked, root5Node31Step1Chunk5_5_checked, root5Node31Step1Chunk6_0_checked, root5Node31Step1Chunk6_1_checked, root5Node31Step1Chunk6_2_checked, root5Node31Step1Chunk6_3_checked, root5Node31Step1Chunk6_4_checked, root5Node31Step1Chunk6_5_checked, root5Node31Step1Chunk7_0_checked, root5Node31Step1Chunk7_1_checked, root5Node31Step1Chunk7_2_checked, root5Node31Step1Chunk7_3_checked, root5Node31Step1Chunk7_4_checked, root5Node31Step1Chunk7_5_checked, root5Node31Step1Chunk8_0_checked, root5Node31Step1Chunk8_1_checked, root5Node31Step1Chunk8_2_checked, root5Node31Step1Chunk8_3_checked, root5Node31Step1Chunk8_4_checked, root5Node31Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
