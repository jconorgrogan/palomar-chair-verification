module

public import SpectreFinite.RadiusFourRoot0Part12
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable0
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node38Domains0 : Domains 61 State := restrict root0Node30Domains1 26 (8,4)
def root0Node38Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,4)]
  | 9 => some [(1,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(7,4)]
  | 51 => some [(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2),(6,0)]
  | 57 => some [(1,1),(7,1)]
  | 58 => some [(4,1),(7,5)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node38Domains0_fast_eq : root0Node38Domains0 = expandDomains root0Node38Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node38Domains0 v = expandDomains root0Node38Domains0Fast v from by decide) v
def root0Node38Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(0,3)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,4)]
  | 9 => [(1,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(4,3)]
  | 25 => [(7,5)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(3,0),(7,0)]
  | 50 => [(7,4)]
  | 51 => [(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(0,5),(6,3)]
  | 55 => [(4,4),(7,2)]
  | 56 => [(0,2)]
  | 57 => [(1,1)]
  | 58 => [(4,1)]
  | 59 => [(0,2),(6,0)]
  | _ => [(1,1),(7,1)]
def root0Node38Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,4)]
  | 9 => some [(1,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(3,0),(7,0)]
  | 50 => some [(7,4)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(0,5),(6,3)]
  | 55 => some [(4,4),(7,2)]
  | 56 => some [(0,2)]
  | 57 => some [(1,1)]
  | 58 => some [(4,1)]
  | 59 => some [(0,2),(6,0)]
  | _ => some [(1,1),(7,1)]
theorem root0Node38Domains1_fast_eq : root0Node38Domains1 = expandDomains root0Node38Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node38Domains1 v = expandDomains root0Node38Domains1Fast v from by decide) v
theorem root0Node38Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root0Node38Domains0 root0Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains0 root0Node38Domains1
    root0Node38Domains0Fast root0Node38Domains1Fast
    root0Node38Domains0_fast_eq root0Node38Domains1_fast_eq (by decide)
theorem root0Node38Step1_checked :
    checkReplacement table37 root0Node38Domains0 root0Node38Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node38Step1Chunk0_0_checked, root0Node38Step1Chunk0_1_checked, root0Node38Step1Chunk0_2_checked, root0Node38Step1Chunk0_3_checked, root0Node38Step1Chunk0_4_checked, root0Node38Step1Chunk0_5_checked, root0Node38Step1Chunk1_0_checked, root0Node38Step1Chunk1_1_checked, root0Node38Step1Chunk1_2_checked, root0Node38Step1Chunk1_3_checked, root0Node38Step1Chunk1_4_checked, root0Node38Step1Chunk1_5_checked, root0Node38Step1Chunk2_0_checked, root0Node38Step1Chunk2_1_checked, root0Node38Step1Chunk2_2_checked, root0Node38Step1Chunk2_3_checked, root0Node38Step1Chunk2_4_checked, root0Node38Step1Chunk2_5_checked, root0Node38Step1Chunk3_0_checked, root0Node38Step1Chunk3_1_checked, root0Node38Step1Chunk3_2_checked, root0Node38Step1Chunk3_3_checked, root0Node38Step1Chunk3_4_checked, root0Node38Step1Chunk3_5_checked, root0Node38Step1Chunk4_0_checked, root0Node38Step1Chunk4_1_checked, root0Node38Step1Chunk4_2_checked, root0Node38Step1Chunk4_3_checked, root0Node38Step1Chunk4_4_checked, root0Node38Step1Chunk4_5_checked, root0Node38Step1Chunk5_0_checked, root0Node38Step1Chunk5_1_checked, root0Node38Step1Chunk5_2_checked, root0Node38Step1Chunk5_3_checked, root0Node38Step1Chunk5_4_checked, root0Node38Step1Chunk5_5_checked, root0Node38Step1Chunk6_0_checked, root0Node38Step1Chunk6_1_checked, root0Node38Step1Chunk6_2_checked, root0Node38Step1Chunk6_3_checked, root0Node38Step1Chunk6_4_checked, root0Node38Step1Chunk6_5_checked, root0Node38Step1Chunk7_0_checked, root0Node38Step1Chunk7_1_checked, root0Node38Step1Chunk7_2_checked, root0Node38Step1Chunk7_3_checked, root0Node38Step1Chunk7_4_checked, root0Node38Step1Chunk7_5_checked, root0Node38Step1Chunk8_0_checked, root0Node38Step1Chunk8_1_checked, root0Node38Step1Chunk8_2_checked, root0Node38Step1Chunk8_3_checked, root0Node38Step1Chunk8_4_checked, root0Node38Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node38Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(3,5)]
  | 3 => [(0,3)]
  | 4 => [(4,1)]
  | 5 => [(4,4)]
  | 6 => [(1,4)]
  | 7 => [(0,5)]
  | 8 => [(2,4)]
  | 9 => [(1,3)]
  | 10 => [(5,2)]
  | 11 => [(7,1)]
  | 12 => [(7,5)]
  | 13 => [(6,0)]
  | 14 => [(7,1)]
  | 15 => [(6,5)]
  | 16 => [(0,4)]
  | 17 => [(5,4)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(8,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(7,0)]
  | 24 => [(4,3)]
  | 25 => [(7,5)]
  | 26 => [(8,4)]
  | 27 => [(6,4)]
  | 28 => [(1,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(7,4)]
  | 33 => [(1,3)]
  | 34 => [(8,2)]
  | 35 => [(7,5)]
  | 36 => [(0,3)]
  | 37 => [(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(8,1)]
  | 41 => [(6,5)]
  | 42 => [(0,4)]
  | 43 => [(4,2)]
  | 44 => [(5,3)]
  | 45 => [(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(8,5)]
  | 49 => [(7,0)]
  | 50 => [(7,4)]
  | 51 => [(6,3)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(6,3)]
  | 55 => [(7,2)]
  | 56 => [(0,2)]
  | 57 => [(1,1)]
  | 58 => [(4,1)]
  | 59 => [(0,2)]
  | _ => [(1,1)]
def root0Node38Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(3,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4)]
  | 6 => some [(1,4)]
  | 7 => some [(0,5)]
  | 8 => some [(2,4)]
  | 9 => some [(1,3)]
  | 10 => some [(5,2)]
  | 11 => some [(7,1)]
  | 12 => some [(7,5)]
  | 13 => some [(6,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,5)]
  | 16 => some [(0,4)]
  | 17 => some [(5,4)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(7,0)]
  | 24 => some [(4,3)]
  | 25 => some [(7,5)]
  | 26 => some [(8,4)]
  | 27 => some [(6,4)]
  | 28 => some [(1,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(7,4)]
  | 33 => some [(1,3)]
  | 34 => some [(8,2)]
  | 35 => some [(7,5)]
  | 36 => some [(0,3)]
  | 37 => some [(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(8,1)]
  | 41 => some [(6,5)]
  | 42 => some [(0,4)]
  | 43 => some [(4,2)]
  | 44 => some [(5,3)]
  | 45 => some [(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(8,5)]
  | 49 => some [(7,0)]
  | 50 => some [(7,4)]
  | 51 => some [(6,3)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(6,3)]
  | 55 => some [(7,2)]
  | 56 => some [(0,2)]
  | 57 => some [(1,1)]
  | 58 => some [(4,1)]
  | 59 => some [(0,2)]
  | _ => some [(1,1)]
theorem root0Node38Domains2_fast_eq : root0Node38Domains2 = expandDomains root0Node38Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node38Domains2 v = expandDomains root0Node38Domains2Fast v from by decide) v
theorem root0Node38Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root0Node38Domains1 root0Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node38Domains1 root0Node38Domains2
    root0Node38Domains1Fast root0Node38Domains2Fast
    root0Node38Domains1_fast_eq root0Node38Domains2_fast_eq (by decide)
theorem root0Node38Step2_checked :
    checkReplacement table40 root0Node38Domains1 root0Node38Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node38Step2Chunk0_0_checked, root0Node38Step2Chunk0_1_checked, root0Node38Step2Chunk0_2_checked, root0Node38Step2Chunk0_3_checked, root0Node38Step2Chunk0_4_checked, root0Node38Step2Chunk0_5_checked, root0Node38Step2Chunk1_0_checked, root0Node38Step2Chunk1_1_checked, root0Node38Step2Chunk1_2_checked, root0Node38Step2Chunk1_3_checked, root0Node38Step2Chunk1_4_checked, root0Node38Step2Chunk1_5_checked, root0Node38Step2Chunk2_0_checked, root0Node38Step2Chunk2_1_checked, root0Node38Step2Chunk2_2_checked, root0Node38Step2Chunk2_3_checked, root0Node38Step2Chunk2_4_checked, root0Node38Step2Chunk2_5_checked, root0Node38Step2Chunk3_0_checked, root0Node38Step2Chunk3_1_checked, root0Node38Step2Chunk3_2_checked, root0Node38Step2Chunk3_3_checked, root0Node38Step2Chunk3_4_checked, root0Node38Step2Chunk3_5_checked, root0Node38Step2Chunk4_0_checked, root0Node38Step2Chunk4_1_checked, root0Node38Step2Chunk4_2_checked, root0Node38Step2Chunk4_3_checked, root0Node38Step2Chunk4_4_checked, root0Node38Step2Chunk4_5_checked, root0Node38Step2Chunk5_0_checked, root0Node38Step2Chunk5_1_checked, root0Node38Step2Chunk5_2_checked, root0Node38Step2Chunk5_3_checked, root0Node38Step2Chunk5_4_checked, root0Node38Step2Chunk5_5_checked, root0Node38Step2Chunk6_0_checked, root0Node38Step2Chunk6_1_checked, root0Node38Step2Chunk6_2_checked, root0Node38Step2Chunk6_3_checked, root0Node38Step2Chunk6_4_checked, root0Node38Step2Chunk6_5_checked, root0Node38Step2Chunk7_0_checked, root0Node38Step2Chunk7_1_checked, root0Node38Step2Chunk7_2_checked, root0Node38Step2Chunk7_3_checked, root0Node38Step2Chunk7_4_checked, root0Node38Step2Chunk7_5_checked, root0Node38Step2Chunk8_0_checked, root0Node38Step2Chunk8_1_checked, root0Node38Step2Chunk8_2_checked, root0Node38Step2Chunk8_3_checked, root0Node38Step2Chunk8_4_checked, root0Node38Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root0Node38Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node38Domains2 (.output 17) = true := by decide
def root0Node39Domains0 : Domains 61 State := restrict root0Node27Domains1 2 (7,5)
def root0Node39Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4),(7,2)]
  | 6 => some [(1,4),(7,4)]
  | 7 => some [(0,5),(6,3)]
  | 8 => some [(2,2),(2,4)]
  | 9 => some [(1,3),(3,3)]
  | 10 => some [(5,2)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(7,5)]
  | 13 => some [(0,2),(6,0)]
  | 14 => some [(1,1),(7,1)]
  | 15 => some [(0,1),(6,5)]
  | 16 => some [(0,4),(6,2)]
  | 17 => some [(5,4),(8,4)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2),(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0),(7,0)]
  | 24 => some [(4,3),(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0),(7,4)]
  | 33 => some [(1,3),(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1),(8,1)]
  | 41 => some [(0,1),(6,5)]
  | 42 => some [(0,4),(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0),(3,0),(7,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node39Domains0_fast_eq : root0Node39Domains0 = expandDomains root0Node39Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node39Domains0 v = expandDomains root0Node39Domains0Fast v from by decide) v
def root0Node39Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(4,1)]
  | 5 => [(4,4),(7,2)]
  | 6 => [(1,4),(7,4)]
  | 7 => [(6,3)]
  | 8 => [(2,2)]
  | 9 => [(3,3)]
  | 10 => [(5,2)]
  | 11 => [(1,1),(7,1)]
  | 12 => [(4,1),(7,5)]
  | 13 => [(0,2)]
  | 14 => [(1,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(4,0),(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(5,1),(5,4),(8,4)]
  | 27 => [(0,1),(6,4)]
  | 28 => [(1,2),(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5),(8,5)]
  | 36 => [(0,3),(1,0)]
  | 37 => [(7,1),(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(4,2),(8,2)]
  | 44 => [(5,0),(5,3)]
  | 45 => [(4,5),(5,5),(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(1,0)]
  | 50 => [(1,4),(3,4),(5,4),(7,4)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,3)]
  | 55 => [(4,4),(7,2),(8,2)]
  | 56 => [(0,2),(1,5),(6,0)]
  | 57 => [(1,1),(6,1),(7,1)]
  | 58 => [(4,1),(7,5),(8,1)]
  | 59 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node39Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(4,4),(7,2)]
  | 6 => some [(1,4),(7,4)]
  | 7 => some [(6,3)]
  | 8 => some [(2,2)]
  | 9 => some [(3,3)]
  | 10 => some [(5,2)]
  | 11 => some [(1,1),(7,1)]
  | 12 => some [(4,1),(7,5)]
  | 13 => some [(0,2)]
  | 14 => some [(1,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node39Domains1_fast_eq : root0Node39Domains1 = expandDomains root0Node39Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node39Domains1 v = expandDomains root0Node39Domains1Fast v from by decide) v
theorem root0Node39Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root0Node39Domains0 root0Node39Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains0 root0Node39Domains1
    root0Node39Domains0Fast root0Node39Domains1Fast
    root0Node39Domains0_fast_eq root0Node39Domains1_fast_eq (by decide)
theorem root0Node39Step1_checked :
    checkReplacement table23 root0Node39Domains0 root0Node39Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node39Step1Chunk0_0_checked, root0Node39Step1Chunk0_1_checked, root0Node39Step1Chunk0_2_checked, root0Node39Step1Chunk0_3_checked, root0Node39Step1Chunk0_4_checked, root0Node39Step1Chunk0_5_checked, root0Node39Step1Chunk1_0_checked, root0Node39Step1Chunk1_1_checked, root0Node39Step1Chunk1_2_checked, root0Node39Step1Chunk1_3_checked, root0Node39Step1Chunk1_4_checked, root0Node39Step1Chunk1_5_checked, root0Node39Step1Chunk2_0_checked, root0Node39Step1Chunk2_1_checked, root0Node39Step1Chunk2_2_checked, root0Node39Step1Chunk2_3_checked, root0Node39Step1Chunk2_4_checked, root0Node39Step1Chunk2_5_checked, root0Node39Step1Chunk3_0_checked, root0Node39Step1Chunk3_1_checked, root0Node39Step1Chunk3_2_checked, root0Node39Step1Chunk3_3_checked, root0Node39Step1Chunk3_4_checked, root0Node39Step1Chunk3_5_checked, root0Node39Step1Chunk4_0_checked, root0Node39Step1Chunk4_1_checked, root0Node39Step1Chunk4_2_checked, root0Node39Step1Chunk4_3_checked, root0Node39Step1Chunk4_4_checked, root0Node39Step1Chunk4_5_checked, root0Node39Step1Chunk5_0_checked, root0Node39Step1Chunk5_1_checked, root0Node39Step1Chunk5_2_checked, root0Node39Step1Chunk5_3_checked, root0Node39Step1Chunk5_4_checked, root0Node39Step1Chunk5_5_checked, root0Node39Step1Chunk6_0_checked, root0Node39Step1Chunk6_1_checked, root0Node39Step1Chunk6_2_checked, root0Node39Step1Chunk6_3_checked, root0Node39Step1Chunk6_4_checked, root0Node39Step1Chunk6_5_checked, root0Node39Step1Chunk7_0_checked, root0Node39Step1Chunk7_1_checked, root0Node39Step1Chunk7_2_checked, root0Node39Step1Chunk7_3_checked, root0Node39Step1Chunk7_4_checked, root0Node39Step1Chunk7_5_checked, root0Node39Step1Chunk8_0_checked, root0Node39Step1Chunk8_1_checked, root0Node39Step1Chunk8_2_checked, root0Node39Step1Chunk8_3_checked, root0Node39Step1Chunk8_4_checked, root0Node39Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node39Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(4,1)]
  | 5 => [(7,2)]
  | 6 => [(7,4)]
  | 7 => [(6,3)]
  | 8 => [(2,2)]
  | 9 => [(3,3)]
  | 10 => [(5,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1)]
  | 13 => [(0,2)]
  | 14 => [(1,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(4,0),(8,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(5,1),(5,4),(8,4)]
  | 27 => [(0,1),(6,4)]
  | 28 => [(1,2),(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(7,5),(8,5)]
  | 36 => [(0,3),(1,0)]
  | 37 => [(7,1),(8,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(4,2),(8,2)]
  | 44 => [(5,0),(5,3)]
  | 45 => [(4,5),(5,5),(8,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(1,0)]
  | 50 => [(1,4),(3,4),(5,4),(7,4)]
  | 51 => [(0,0),(0,5),(6,3)]
  | 52 => [(4,4),(7,2)]
  | 53 => [(1,4),(7,4)]
  | 54 => [(0,5),(1,3),(6,3)]
  | 55 => [(4,4),(7,2),(8,2)]
  | 56 => [(0,2),(1,5),(6,0)]
  | 57 => [(1,1),(6,1),(7,1)]
  | 58 => [(4,1),(7,5),(8,1)]
  | 59 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node39Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(6,3)]
  | 8 => some [(2,2)]
  | 9 => some [(3,3)]
  | 10 => some [(5,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1)]
  | 13 => some [(0,2)]
  | 14 => some [(1,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(4,0),(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node39Domains2_fast_eq : root0Node39Domains2 = expandDomains root0Node39Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node39Domains2 v = expandDomains root0Node39Domains2Fast v from by decide) v
theorem root0Node39Step2Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root0Node39Domains1 root0Node39Domains2 = true := by
  exact checkNarrowing_of_fast _ root0Node39Domains1 root0Node39Domains2
    root0Node39Domains1Fast root0Node39Domains2Fast
    root0Node39Domains1_fast_eq root0Node39Domains2_fast_eq (by decide)
theorem root0Node39Step2_checked :
    checkReplacement table0 root0Node39Domains1 root0Node39Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node39Step2Chunk0_0_checked, root0Node39Step2Chunk0_1_checked, root0Node39Step2Chunk0_2_checked, root0Node39Step2Chunk0_3_checked, root0Node39Step2Chunk0_4_checked, root0Node39Step2Chunk0_5_checked, root0Node39Step2Chunk1_0_checked, root0Node39Step2Chunk1_1_checked, root0Node39Step2Chunk1_2_checked, root0Node39Step2Chunk1_3_checked, root0Node39Step2Chunk1_4_checked, root0Node39Step2Chunk1_5_checked, root0Node39Step2Chunk2_0_checked, root0Node39Step2Chunk2_1_checked, root0Node39Step2Chunk2_2_checked, root0Node39Step2Chunk2_3_checked, root0Node39Step2Chunk2_4_checked, root0Node39Step2Chunk2_5_checked, root0Node39Step2Chunk3_0_checked, root0Node39Step2Chunk3_1_checked, root0Node39Step2Chunk3_2_checked, root0Node39Step2Chunk3_3_checked, root0Node39Step2Chunk3_4_checked, root0Node39Step2Chunk3_5_checked, root0Node39Step2Chunk4_0_checked, root0Node39Step2Chunk4_1_checked, root0Node39Step2Chunk4_2_checked, root0Node39Step2Chunk4_3_checked, root0Node39Step2Chunk4_4_checked, root0Node39Step2Chunk4_5_checked, root0Node39Step2Chunk5_0_checked, root0Node39Step2Chunk5_1_checked, root0Node39Step2Chunk5_2_checked, root0Node39Step2Chunk5_3_checked, root0Node39Step2Chunk5_4_checked, root0Node39Step2Chunk5_5_checked, root0Node39Step2Chunk6_0_checked, root0Node39Step2Chunk6_1_checked, root0Node39Step2Chunk6_2_checked, root0Node39Step2Chunk6_3_checked, root0Node39Step2Chunk6_4_checked, root0Node39Step2Chunk6_5_checked, root0Node39Step2Chunk7_0_checked, root0Node39Step2Chunk7_1_checked, root0Node39Step2Chunk7_2_checked, root0Node39Step2Chunk7_3_checked, root0Node39Step2Chunk7_4_checked, root0Node39Step2Chunk7_5_checked, root0Node39Step2Chunk8_0_checked, root0Node39Step2Chunk8_1_checked, root0Node39Step2Chunk8_2_checked, root0Node39Step2Chunk8_3_checked, root0Node39Step2Chunk8_4_checked, root0Node39Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root0Node40Domains0 : Domains 61 State := restrict root0Node39Domains2 18 (4,0)
def root0Node40Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(6,3)]
  | 8 => some [(2,2)]
  | 9 => some [(3,3)]
  | 10 => some [(5,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1)]
  | 13 => some [(0,2)]
  | 14 => some [(1,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,1),(5,4),(8,4)]
  | 27 => some [(0,1),(6,4)]
  | 28 => some [(1,2),(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(7,5),(8,5)]
  | 36 => some [(0,3),(1,0)]
  | 37 => some [(7,1),(8,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(4,2),(8,2)]
  | 44 => some [(5,0),(5,3)]
  | 45 => some [(4,5),(5,5),(8,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(1,4),(3,4),(5,4),(7,4)]
  | 51 => some [(0,0),(0,5),(6,3)]
  | 52 => some [(4,4),(7,2)]
  | 53 => some [(1,4),(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(0,2),(1,5),(6,0)]
  | 57 => some [(1,1),(6,1),(7,1)]
  | 58 => some [(4,1),(7,5),(8,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node40Domains0_fast_eq : root0Node40Domains0 = expandDomains root0Node40Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node40Domains0 v = expandDomains root0Node40Domains0Fast v from by decide) v
def root0Node40Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(7,0)]
  | 1 => [(4,3)]
  | 2 => [(7,5)]
  | 3 => [(0,3)]
  | 4 => [(4,1)]
  | 5 => [(7,2)]
  | 6 => [(7,4)]
  | 7 => [(6,3)]
  | 8 => [(2,2)]
  | 9 => [(3,3)]
  | 10 => [(5,2)]
  | 11 => [(1,1)]
  | 12 => [(4,1)]
  | 13 => [(0,2)]
  | 14 => [(1,1)]
  | 15 => [(0,1)]
  | 16 => [(6,2)]
  | 17 => [(8,4)]
  | 18 => [(4,0)]
  | 19 => [(7,3)]
  | 20 => [(5,2)]
  | 21 => [(5,0)]
  | 22 => [(4,5)]
  | 23 => [(1,0)]
  | 24 => [(7,1)]
  | 25 => [(7,5)]
  | 26 => [(5,1)]
  | 27 => [(0,1)]
  | 28 => [(6,2)]
  | 29 => [(8,4)]
  | 30 => [(0,0)]
  | 31 => [(7,2)]
  | 32 => [(4,0)]
  | 33 => [(7,3)]
  | 34 => [(4,2),(8,2)]
  | 35 => [(8,5)]
  | 36 => [(1,0)]
  | 37 => [(7,1)]
  | 38 => [(1,5)]
  | 39 => [(6,1)]
  | 40 => [(5,1)]
  | 41 => [(0,1)]
  | 42 => [(6,2)]
  | 43 => [(8,2)]
  | 44 => [(5,0)]
  | 45 => [(4,5)]
  | 46 => [(7,0)]
  | 47 => [(8,3)]
  | 48 => [(5,5),(8,5)]
  | 49 => [(1,0)]
  | 50 => [(5,4)]
  | 51 => [(0,0)]
  | 52 => [(7,2)]
  | 53 => [(7,4)]
  | 54 => [(0,5),(1,3),(6,3)]
  | 55 => [(4,4),(7,2),(8,2)]
  | 56 => [(1,5)]
  | 57 => [(6,1)]
  | 58 => [(4,1)]
  | 59 => [(0,2),(6,0),(6,5)]
  | _ => [(0,4),(1,1),(7,1)]
def root0Node40Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(7,0)]
  | 1 => some [(4,3)]
  | 2 => some [(7,5)]
  | 3 => some [(0,3)]
  | 4 => some [(4,1)]
  | 5 => some [(7,2)]
  | 6 => some [(7,4)]
  | 7 => some [(6,3)]
  | 8 => some [(2,2)]
  | 9 => some [(3,3)]
  | 10 => some [(5,2)]
  | 11 => some [(1,1)]
  | 12 => some [(4,1)]
  | 13 => some [(0,2)]
  | 14 => some [(1,1)]
  | 15 => some [(0,1)]
  | 16 => some [(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(4,0)]
  | 19 => some [(7,3)]
  | 20 => some [(5,2)]
  | 21 => some [(5,0)]
  | 22 => some [(4,5)]
  | 23 => some [(1,0)]
  | 24 => some [(7,1)]
  | 25 => some [(7,5)]
  | 26 => some [(5,1)]
  | 27 => some [(0,1)]
  | 28 => some [(6,2)]
  | 29 => some [(8,4)]
  | 30 => some [(0,0)]
  | 31 => some [(7,2)]
  | 32 => some [(4,0)]
  | 33 => some [(7,3)]
  | 34 => some [(4,2),(8,2)]
  | 35 => some [(8,5)]
  | 36 => some [(1,0)]
  | 37 => some [(7,1)]
  | 38 => some [(1,5)]
  | 39 => some [(6,1)]
  | 40 => some [(5,1)]
  | 41 => some [(0,1)]
  | 42 => some [(6,2)]
  | 43 => some [(8,2)]
  | 44 => some [(5,0)]
  | 45 => some [(4,5)]
  | 46 => some [(7,0)]
  | 47 => some [(8,3)]
  | 48 => some [(5,5),(8,5)]
  | 49 => some [(1,0)]
  | 50 => some [(5,4)]
  | 51 => some [(0,0)]
  | 52 => some [(7,2)]
  | 53 => some [(7,4)]
  | 54 => some [(0,5),(1,3),(6,3)]
  | 55 => some [(4,4),(7,2),(8,2)]
  | 56 => some [(1,5)]
  | 57 => some [(6,1)]
  | 58 => some [(4,1)]
  | 59 => some [(0,2),(6,0),(6,5)]
  | _ => some [(0,4),(1,1),(7,1)]
theorem root0Node40Domains1_fast_eq : root0Node40Domains1 = expandDomains root0Node40Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root0Node40Domains1 v = expandDomains root0Node40Domains1Fast v from by decide) v
theorem root0Node40Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root0Node40Domains0 root0Node40Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node40Domains0 root0Node40Domains1
    root0Node40Domains0Fast root0Node40Domains1Fast
    root0Node40Domains0_fast_eq root0Node40Domains1_fast_eq (by decide)
theorem root0Node40Step1_checked :
    checkReplacement table37 root0Node40Domains0 root0Node40Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node40Step1Chunk0_0_checked, root0Node40Step1Chunk0_1_checked, root0Node40Step1Chunk0_2_checked, root0Node40Step1Chunk0_3_checked, root0Node40Step1Chunk0_4_checked, root0Node40Step1Chunk0_5_checked, root0Node40Step1Chunk1_0_checked, root0Node40Step1Chunk1_1_checked, root0Node40Step1Chunk1_2_checked, root0Node40Step1Chunk1_3_checked, root0Node40Step1Chunk1_4_checked, root0Node40Step1Chunk1_5_checked, root0Node40Step1Chunk2_0_checked, root0Node40Step1Chunk2_1_checked, root0Node40Step1Chunk2_2_checked, root0Node40Step1Chunk2_3_checked, root0Node40Step1Chunk2_4_checked, root0Node40Step1Chunk2_5_checked, root0Node40Step1Chunk3_0_checked, root0Node40Step1Chunk3_1_checked, root0Node40Step1Chunk3_2_checked, root0Node40Step1Chunk3_3_checked, root0Node40Step1Chunk3_4_checked, root0Node40Step1Chunk3_5_checked, root0Node40Step1Chunk4_0_checked, root0Node40Step1Chunk4_1_checked, root0Node40Step1Chunk4_2_checked, root0Node40Step1Chunk4_3_checked, root0Node40Step1Chunk4_4_checked, root0Node40Step1Chunk4_5_checked, root0Node40Step1Chunk5_0_checked, root0Node40Step1Chunk5_1_checked, root0Node40Step1Chunk5_2_checked, root0Node40Step1Chunk5_3_checked, root0Node40Step1Chunk5_4_checked, root0Node40Step1Chunk5_5_checked, root0Node40Step1Chunk6_0_checked, root0Node40Step1Chunk6_1_checked, root0Node40Step1Chunk6_2_checked, root0Node40Step1Chunk6_3_checked, root0Node40Step1Chunk6_4_checked, root0Node40Step1Chunk6_5_checked, root0Node40Step1Chunk7_0_checked, root0Node40Step1Chunk7_1_checked, root0Node40Step1Chunk7_2_checked, root0Node40Step1Chunk7_3_checked, root0Node40Step1Chunk7_4_checked, root0Node40Step1Chunk7_5_checked, root0Node40Step1Chunk8_0_checked, root0Node40Step1Chunk8_1_checked, root0Node40Step1Chunk8_2_checked, root0Node40Step1Chunk8_3_checked, root0Node40Step1Chunk8_4_checked, root0Node40Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
