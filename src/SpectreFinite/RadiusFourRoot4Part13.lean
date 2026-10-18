module

public import SpectreFinite.RadiusFourRoot4Part12
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable0
public import SpectreFinite.RadiusFourTable20
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node36Domains0 : Domains 61 State := restrict root4Node30Domains2 26 (6,2)
def root4Node36Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(6,3)]
  | 6 => some [(2,2)]
  | 7 => some [(3,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(5,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0),(8,0)]
  | 34 => some [(4,5),(7,3)]
  | 35 => some [(7,1),(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
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
theorem root4Node36Domains0_fast_eq : root4Node36Domains0 = expandDomains root4Node36Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node36Domains0 v = expandDomains root4Node36Domains0Fast v from by decide) v
def root4Node36Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(6,3)]
  | 6 => [(2,2)]
  | 7 => [(3,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(5,2)]
  | 19 => [(5,0)]
  | 20 => [(4,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(6,2)]
  | 27 => [(8,4)]
  | 28 => [(0,0)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
  | 33 => [(5,0),(8,0)]
  | 34 => [(4,5),(7,3)]
  | 35 => [(7,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(4,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(8,5)]
  | 47 => [(1,0)]
  | 48 => [(7,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(6,3)]
  | 53 => [(7,2)]
  | 54 => [(4,0),(5,0),(8,0)]
  | 55 => [(4,5),(7,3)]
  | 56 => [(4,1)]
  | 57 => [(0,2)]
  | 58 => [(1,1)]
  | 59 => [(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,4)]
def root4Node36Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(6,3)]
  | 6 => some [(2,2)]
  | 7 => some [(3,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(5,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0),(8,0)]
  | 34 => some [(4,5),(7,3)]
  | 35 => some [(7,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(7,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(6,3)]
  | 53 => some [(7,2)]
  | 54 => some [(4,0),(5,0),(8,0)]
  | 55 => some [(4,5),(7,3)]
  | 56 => some [(4,1)]
  | 57 => some [(0,2)]
  | 58 => some [(1,1)]
  | 59 => some [(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,4)]
theorem root4Node36Domains1_fast_eq : root4Node36Domains1 = expandDomains root4Node36Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node36Domains1 v = expandDomains root4Node36Domains1Fast v from by decide) v
theorem root4Node36Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root4Node36Domains0 root4Node36Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains0 root4Node36Domains1
    root4Node36Domains0Fast root4Node36Domains1Fast
    root4Node36Domains0_fast_eq root4Node36Domains1_fast_eq (by decide)
theorem root4Node36Step1_checked :
    checkReplacement table37 root4Node36Domains0 root4Node36Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node36Step1Chunk0_0_checked, root4Node36Step1Chunk0_1_checked, root4Node36Step1Chunk0_2_checked, root4Node36Step1Chunk0_3_checked, root4Node36Step1Chunk0_4_checked, root4Node36Step1Chunk0_5_checked, root4Node36Step1Chunk1_0_checked, root4Node36Step1Chunk1_1_checked, root4Node36Step1Chunk1_2_checked, root4Node36Step1Chunk1_3_checked, root4Node36Step1Chunk1_4_checked, root4Node36Step1Chunk1_5_checked, root4Node36Step1Chunk2_0_checked, root4Node36Step1Chunk2_1_checked, root4Node36Step1Chunk2_2_checked, root4Node36Step1Chunk2_3_checked, root4Node36Step1Chunk2_4_checked, root4Node36Step1Chunk2_5_checked, root4Node36Step1Chunk3_0_checked, root4Node36Step1Chunk3_1_checked, root4Node36Step1Chunk3_2_checked, root4Node36Step1Chunk3_3_checked, root4Node36Step1Chunk3_4_checked, root4Node36Step1Chunk3_5_checked, root4Node36Step1Chunk4_0_checked, root4Node36Step1Chunk4_1_checked, root4Node36Step1Chunk4_2_checked, root4Node36Step1Chunk4_3_checked, root4Node36Step1Chunk4_4_checked, root4Node36Step1Chunk4_5_checked, root4Node36Step1Chunk5_0_checked, root4Node36Step1Chunk5_1_checked, root4Node36Step1Chunk5_2_checked, root4Node36Step1Chunk5_3_checked, root4Node36Step1Chunk5_4_checked, root4Node36Step1Chunk5_5_checked, root4Node36Step1Chunk6_0_checked, root4Node36Step1Chunk6_1_checked, root4Node36Step1Chunk6_2_checked, root4Node36Step1Chunk6_3_checked, root4Node36Step1Chunk6_4_checked, root4Node36Step1Chunk6_5_checked, root4Node36Step1Chunk7_0_checked, root4Node36Step1Chunk7_1_checked, root4Node36Step1Chunk7_2_checked, root4Node36Step1Chunk7_3_checked, root4Node36Step1Chunk7_4_checked, root4Node36Step1Chunk7_5_checked, root4Node36Step1Chunk8_0_checked, root4Node36Step1Chunk8_1_checked, root4Node36Step1Chunk8_2_checked, root4Node36Step1Chunk8_3_checked, root4Node36Step1Chunk8_4_checked, root4Node36Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node36Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,5)]
  | 1 => [(0,3)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(6,3)]
  | 6 => [(2,2)]
  | 7 => [(3,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(5,2)]
  | 19 => [(5,0)]
  | 20 => [(4,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(6,2)]
  | 27 => [(8,4)]
  | 28 => [(0,0)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
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
def root4Node36Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,5)]
  | 1 => some [(0,3)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(6,3)]
  | 6 => some [(2,2)]
  | 7 => some [(3,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(5,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
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
theorem root4Node36Domains2_fast_eq : root4Node36Domains2 = expandDomains root4Node36Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node36Domains2 v = expandDomains root4Node36Domains2Fast v from by decide) v
theorem root4Node36Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root4Node36Domains1 root4Node36Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node36Domains1 root4Node36Domains2
    root4Node36Domains1Fast root4Node36Domains2Fast
    root4Node36Domains1_fast_eq root4Node36Domains2_fast_eq (by decide)
theorem root4Node36Step2_checked :
    checkReplacement table40 root4Node36Domains1 root4Node36Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node36Step2Chunk0_0_checked, root4Node36Step2Chunk0_1_checked, root4Node36Step2Chunk0_2_checked, root4Node36Step2Chunk0_3_checked, root4Node36Step2Chunk0_4_checked, root4Node36Step2Chunk0_5_checked, root4Node36Step2Chunk1_0_checked, root4Node36Step2Chunk1_1_checked, root4Node36Step2Chunk1_2_checked, root4Node36Step2Chunk1_3_checked, root4Node36Step2Chunk1_4_checked, root4Node36Step2Chunk1_5_checked, root4Node36Step2Chunk2_0_checked, root4Node36Step2Chunk2_1_checked, root4Node36Step2Chunk2_2_checked, root4Node36Step2Chunk2_3_checked, root4Node36Step2Chunk2_4_checked, root4Node36Step2Chunk2_5_checked, root4Node36Step2Chunk3_0_checked, root4Node36Step2Chunk3_1_checked, root4Node36Step2Chunk3_2_checked, root4Node36Step2Chunk3_3_checked, root4Node36Step2Chunk3_4_checked, root4Node36Step2Chunk3_5_checked, root4Node36Step2Chunk4_0_checked, root4Node36Step2Chunk4_1_checked, root4Node36Step2Chunk4_2_checked, root4Node36Step2Chunk4_3_checked, root4Node36Step2Chunk4_4_checked, root4Node36Step2Chunk4_5_checked, root4Node36Step2Chunk5_0_checked, root4Node36Step2Chunk5_1_checked, root4Node36Step2Chunk5_2_checked, root4Node36Step2Chunk5_3_checked, root4Node36Step2Chunk5_4_checked, root4Node36Step2Chunk5_5_checked, root4Node36Step2Chunk6_0_checked, root4Node36Step2Chunk6_1_checked, root4Node36Step2Chunk6_2_checked, root4Node36Step2Chunk6_3_checked, root4Node36Step2Chunk6_4_checked, root4Node36Step2Chunk6_5_checked, root4Node36Step2Chunk7_0_checked, root4Node36Step2Chunk7_1_checked, root4Node36Step2Chunk7_2_checked, root4Node36Step2Chunk7_3_checked, root4Node36Step2Chunk7_4_checked, root4Node36Step2Chunk7_5_checked, root4Node36Step2Chunk8_0_checked, root4Node36Step2Chunk8_1_checked, root4Node36Step2Chunk8_2_checked, root4Node36Step2Chunk8_3_checked, root4Node36Step2Chunk8_4_checked, root4Node36Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root4Node36Leaf_checked :
    checkCover 1 constraints root4Outputs root4Node36Domains2 (.output 17) = true := by decide
def root4Node37Domains0 : Domains 61 State := restrict root4Node27Domains1 7 (7,3)
def root4Node37Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5),(1,2),(3,2),(6,3)]
  | 6 => some [(2,0),(2,2),(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3),(8,3)]
  | 11 => some [(0,2),(0,3),(6,0),(6,1)]
  | 12 => some [(1,1),(3,1),(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(4,2),(5,2),(7,0),(8,2)]
  | 19 => some [(5,0),(5,3),(8,3)]
  | 20 => some [(4,5),(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(6,2),(7,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(0,0),(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,5)]
  | 35 => some [(4,1),(7,1),(8,1)]
  | 36 => some [(0,2),(1,5)]
  | 37 => some [(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3),(6,4)]
  | 43 => some [(4,5),(5,2),(5,5),(8,5)]
  | 44 => some [(7,0),(8,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node37Domains0_fast_eq : root4Node37Domains0 = expandDomains root4Node37Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node37Domains0 v = expandDomains root4Node37Domains0Fast v from by decide) v
def root4Node37Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5)]
  | 1 => [(1,1),(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(0,5),(1,2),(3,2)]
  | 6 => [(2,0),(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(0,3),(6,0),(6,1)]
  | 12 => [(3,1),(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(4,2),(7,0),(8,2)]
  | 19 => [(5,0),(5,3),(8,3)]
  | 20 => [(4,5),(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(7,1),(8,1)]
  | 26 => [(1,2),(6,2),(7,2)]
  | 27 => [(7,4),(8,4)]
  | 28 => [(0,0),(6,3)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => [(4,5),(7,3),(8,5)]
  | 35 => [(4,1),(7,1),(8,1)]
  | 36 => [(0,2),(1,5)]
  | 37 => [(1,1),(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(6,3),(6,4)]
  | 43 => [(4,5),(5,2),(5,5),(8,5)]
  | 44 => [(7,0),(8,0)]
  | 45 => [(8,3)]
  | 46 => [(5,5),(8,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1),(7,1)]
  | 49 => [(0,2),(1,5),(7,5)]
  | 50 => [(4,4),(5,4),(7,2),(8,4)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(4,4),(7,2),(8,2)]
  | 54 => [(0,0),(4,0),(5,0),(8,0)]
  | 55 => [(3,2),(4,5),(7,3)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node37Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5)]
  | 1 => some [(1,1),(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5),(1,2),(3,2)]
  | 6 => some [(2,0),(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3),(8,3)]
  | 11 => some [(0,3),(6,0),(6,1)]
  | 12 => some [(3,1),(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(4,2),(7,0),(8,2)]
  | 19 => some [(5,0),(5,3),(8,3)]
  | 20 => some [(4,5),(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(6,2),(7,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(0,0),(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,5)]
  | 35 => some [(4,1),(7,1),(8,1)]
  | 36 => some [(0,2),(1,5)]
  | 37 => some [(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3),(6,4)]
  | 43 => some [(4,5),(5,2),(5,5),(8,5)]
  | 44 => some [(7,0),(8,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node37Domains1_fast_eq : root4Node37Domains1 = expandDomains root4Node37Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node37Domains1 v = expandDomains root4Node37Domains1Fast v from by decide) v
theorem root4Node37Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root4Node37Domains0 root4Node37Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node37Domains0 root4Node37Domains1
    root4Node37Domains0Fast root4Node37Domains1Fast
    root4Node37Domains0_fast_eq root4Node37Domains1_fast_eq (by decide)
theorem root4Node37Step1_checked :
    checkReplacement table0 root4Node37Domains0 root4Node37Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node37Step1Chunk0_0_checked, root4Node37Step1Chunk0_1_checked, root4Node37Step1Chunk0_2_checked, root4Node37Step1Chunk0_3_checked, root4Node37Step1Chunk0_4_checked, root4Node37Step1Chunk0_5_checked, root4Node37Step1Chunk1_0_checked, root4Node37Step1Chunk1_1_checked, root4Node37Step1Chunk1_2_checked, root4Node37Step1Chunk1_3_checked, root4Node37Step1Chunk1_4_checked, root4Node37Step1Chunk1_5_checked, root4Node37Step1Chunk2_0_checked, root4Node37Step1Chunk2_1_checked, root4Node37Step1Chunk2_2_checked, root4Node37Step1Chunk2_3_checked, root4Node37Step1Chunk2_4_checked, root4Node37Step1Chunk2_5_checked, root4Node37Step1Chunk3_0_checked, root4Node37Step1Chunk3_1_checked, root4Node37Step1Chunk3_2_checked, root4Node37Step1Chunk3_3_checked, root4Node37Step1Chunk3_4_checked, root4Node37Step1Chunk3_5_checked, root4Node37Step1Chunk4_0_checked, root4Node37Step1Chunk4_1_checked, root4Node37Step1Chunk4_2_checked, root4Node37Step1Chunk4_3_checked, root4Node37Step1Chunk4_4_checked, root4Node37Step1Chunk4_5_checked, root4Node37Step1Chunk5_0_checked, root4Node37Step1Chunk5_1_checked, root4Node37Step1Chunk5_2_checked, root4Node37Step1Chunk5_3_checked, root4Node37Step1Chunk5_4_checked, root4Node37Step1Chunk5_5_checked, root4Node37Step1Chunk6_0_checked, root4Node37Step1Chunk6_1_checked, root4Node37Step1Chunk6_2_checked, root4Node37Step1Chunk6_3_checked, root4Node37Step1Chunk6_4_checked, root4Node37Step1Chunk6_5_checked, root4Node37Step1Chunk7_0_checked, root4Node37Step1Chunk7_1_checked, root4Node37Step1Chunk7_2_checked, root4Node37Step1Chunk7_3_checked, root4Node37Step1Chunk7_4_checked, root4Node37Step1Chunk7_5_checked, root4Node37Step1Chunk8_0_checked, root4Node37Step1Chunk8_1_checked, root4Node37Step1Chunk8_2_checked, root4Node37Step1Chunk8_3_checked, root4Node37Step1Chunk8_4_checked, root4Node37Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node38Domains0 : Domains 61 State := restrict root4Node37Domains1 0 (0,2)
def root4Node38Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1),(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5),(1,2),(3,2)]
  | 6 => some [(2,0),(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3),(8,3)]
  | 11 => some [(0,3),(6,0),(6,1)]
  | 12 => some [(3,1),(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(4,2),(7,0),(8,2)]
  | 19 => some [(5,0),(5,3),(8,3)]
  | 20 => some [(4,5),(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(6,2),(7,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(0,0),(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,5)]
  | 35 => some [(4,1),(7,1),(8,1)]
  | 36 => some [(0,2),(1,5)]
  | 37 => some [(1,1),(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3),(6,4)]
  | 43 => some [(4,5),(5,2),(5,5),(8,5)]
  | 44 => some [(7,0),(8,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node38Domains0_fast_eq : root4Node38Domains0 = expandDomains root4Node38Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node38Domains0 v = expandDomains root4Node38Domains0Fast v from by decide) v
def root4Node38Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(1,2),(3,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(0,3),(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(5,3),(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(7,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => [(4,5),(7,3),(8,5)]
  | 35 => [(4,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(6,3),(6,4)]
  | 43 => [(5,2)]
  | 44 => [(8,0)]
  | 45 => [(8,3)]
  | 46 => [(5,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1),(7,1)]
  | 49 => [(0,2),(1,5),(7,5)]
  | 50 => [(4,4),(5,4),(7,2),(8,4)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(4,4),(7,2),(8,2)]
  | 54 => [(0,0),(4,0),(5,0),(8,0)]
  | 55 => [(3,2),(4,5),(7,3)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node38Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(1,2),(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3),(8,3)]
  | 11 => some [(0,3),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(5,3),(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,5)]
  | 35 => some [(4,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3),(6,4)]
  | 43 => some [(5,2)]
  | 44 => some [(8,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(4,4),(7,2),(8,2)]
  | 54 => some [(0,0),(4,0),(5,0),(8,0)]
  | 55 => some [(3,2),(4,5),(7,3)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node38Domains1_fast_eq : root4Node38Domains1 = expandDomains root4Node38Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node38Domains1 v = expandDomains root4Node38Domains1Fast v from by decide) v
theorem root4Node38Step1Chunk0_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk0_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk0_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk0_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk0_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk0_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk1_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk2_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk3_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk4_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk5_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk6_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk7_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_0⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_1⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_2⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_3⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_4⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1Chunk8_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_5⟩
      root4Node38Domains0 root4Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains0 root4Node38Domains1
    root4Node38Domains0Fast root4Node38Domains1Fast
    root4Node38Domains0_fast_eq root4Node38Domains1_fast_eq (by decide)
theorem root4Node38Step1_checked :
    checkReplacement table20 root4Node38Domains0 root4Node38Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node38Step1Chunk0_0_checked, root4Node38Step1Chunk0_1_checked, root4Node38Step1Chunk0_2_checked, root4Node38Step1Chunk0_3_checked, root4Node38Step1Chunk0_4_checked, root4Node38Step1Chunk0_5_checked, root4Node38Step1Chunk1_0_checked, root4Node38Step1Chunk1_1_checked, root4Node38Step1Chunk1_2_checked, root4Node38Step1Chunk1_3_checked, root4Node38Step1Chunk1_4_checked, root4Node38Step1Chunk1_5_checked, root4Node38Step1Chunk2_0_checked, root4Node38Step1Chunk2_1_checked, root4Node38Step1Chunk2_2_checked, root4Node38Step1Chunk2_3_checked, root4Node38Step1Chunk2_4_checked, root4Node38Step1Chunk2_5_checked, root4Node38Step1Chunk3_0_checked, root4Node38Step1Chunk3_1_checked, root4Node38Step1Chunk3_2_checked, root4Node38Step1Chunk3_3_checked, root4Node38Step1Chunk3_4_checked, root4Node38Step1Chunk3_5_checked, root4Node38Step1Chunk4_0_checked, root4Node38Step1Chunk4_1_checked, root4Node38Step1Chunk4_2_checked, root4Node38Step1Chunk4_3_checked, root4Node38Step1Chunk4_4_checked, root4Node38Step1Chunk4_5_checked, root4Node38Step1Chunk5_0_checked, root4Node38Step1Chunk5_1_checked, root4Node38Step1Chunk5_2_checked, root4Node38Step1Chunk5_3_checked, root4Node38Step1Chunk5_4_checked, root4Node38Step1Chunk5_5_checked, root4Node38Step1Chunk6_0_checked, root4Node38Step1Chunk6_1_checked, root4Node38Step1Chunk6_2_checked, root4Node38Step1Chunk6_3_checked, root4Node38Step1Chunk6_4_checked, root4Node38Step1Chunk6_5_checked, root4Node38Step1Chunk7_0_checked, root4Node38Step1Chunk7_1_checked, root4Node38Step1Chunk7_2_checked, root4Node38Step1Chunk7_3_checked, root4Node38Step1Chunk7_4_checked, root4Node38Step1Chunk7_5_checked, root4Node38Step1Chunk8_0_checked, root4Node38Step1Chunk8_1_checked, root4Node38Step1Chunk8_2_checked, root4Node38Step1Chunk8_3_checked, root4Node38Step1Chunk8_4_checked, root4Node38Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node38Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(1,2),(3,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(0,3),(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(5,3),(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(6,3)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(4,1)]
  | 36 => [(0,2)]
  | 37 => [(1,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,2)]
  | 44 => [(8,0)]
  | 45 => [(8,3)]
  | 46 => [(5,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4),(5,4),(7,2),(8,4)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(3,2)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(7,1)]
  | 59 => [(1,5)]
  | _ => [(6,1)]
def root4Node38Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(1,2),(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3),(8,3)]
  | 11 => some [(0,3),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(5,3),(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(6,3)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(4,1)]
  | 36 => some [(0,2)]
  | 37 => some [(1,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,2)]
  | 44 => some [(8,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4),(5,4),(7,2),(8,4)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(3,2)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(7,1)]
  | 59 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node38Domains2_fast_eq : root4Node38Domains2 = expandDomains root4Node38Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node38Domains2 v = expandDomains root4Node38Domains2Fast v from by decide) v
theorem root4Node38Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root4Node38Domains1 root4Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node38Domains1 root4Node38Domains2
    root4Node38Domains1Fast root4Node38Domains2Fast
    root4Node38Domains1_fast_eq root4Node38Domains2_fast_eq (by decide)
theorem root4Node38Step2_checked :
    checkReplacement table40 root4Node38Domains1 root4Node38Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node38Step2Chunk0_0_checked, root4Node38Step2Chunk0_1_checked, root4Node38Step2Chunk0_2_checked, root4Node38Step2Chunk0_3_checked, root4Node38Step2Chunk0_4_checked, root4Node38Step2Chunk0_5_checked, root4Node38Step2Chunk1_0_checked, root4Node38Step2Chunk1_1_checked, root4Node38Step2Chunk1_2_checked, root4Node38Step2Chunk1_3_checked, root4Node38Step2Chunk1_4_checked, root4Node38Step2Chunk1_5_checked, root4Node38Step2Chunk2_0_checked, root4Node38Step2Chunk2_1_checked, root4Node38Step2Chunk2_2_checked, root4Node38Step2Chunk2_3_checked, root4Node38Step2Chunk2_4_checked, root4Node38Step2Chunk2_5_checked, root4Node38Step2Chunk3_0_checked, root4Node38Step2Chunk3_1_checked, root4Node38Step2Chunk3_2_checked, root4Node38Step2Chunk3_3_checked, root4Node38Step2Chunk3_4_checked, root4Node38Step2Chunk3_5_checked, root4Node38Step2Chunk4_0_checked, root4Node38Step2Chunk4_1_checked, root4Node38Step2Chunk4_2_checked, root4Node38Step2Chunk4_3_checked, root4Node38Step2Chunk4_4_checked, root4Node38Step2Chunk4_5_checked, root4Node38Step2Chunk5_0_checked, root4Node38Step2Chunk5_1_checked, root4Node38Step2Chunk5_2_checked, root4Node38Step2Chunk5_3_checked, root4Node38Step2Chunk5_4_checked, root4Node38Step2Chunk5_5_checked, root4Node38Step2Chunk6_0_checked, root4Node38Step2Chunk6_1_checked, root4Node38Step2Chunk6_2_checked, root4Node38Step2Chunk6_3_checked, root4Node38Step2Chunk6_4_checked, root4Node38Step2Chunk6_5_checked, root4Node38Step2Chunk7_0_checked, root4Node38Step2Chunk7_1_checked, root4Node38Step2Chunk7_2_checked, root4Node38Step2Chunk7_3_checked, root4Node38Step2Chunk7_4_checked, root4Node38Step2Chunk7_5_checked, root4Node38Step2Chunk8_0_checked, root4Node38Step2Chunk8_1_checked, root4Node38Step2Chunk8_2_checked, root4Node38Step2Chunk8_3_checked, root4Node38Step2Chunk8_4_checked, root4Node38Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
