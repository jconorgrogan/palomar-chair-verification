module

public import SpectreFinite.RadiusFourRoot5Part12
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node38Domains0 : Domains 61 State := restrict root5Node37Domains3 27 (4,0)
def root5Node38Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(1,2),(3,2),(5,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
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
theorem root5Node38Domains0_fast_eq : root5Node38Domains0 = expandDomains root5Node38Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node38Domains0 v = expandDomains root5Node38Domains0Fast v from by decide) v
def root5Node38Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(0,1)]
  | 24 => [(6,2)]
  | 25 => [(8,4)]
  | 26 => [(1,2),(3,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
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
  | _ => [(0,5),(1,3),(6,3)]
def root5Node38Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(1,2),(3,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
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
  | _ => some [(0,5),(1,3),(6,3)]
theorem root5Node38Domains1_fast_eq : root5Node38Domains1 = expandDomains root5Node38Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node38Domains1 v = expandDomains root5Node38Domains1Fast v from by decide) v
theorem root5Node38Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root5Node38Domains0 root5Node38Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains0 root5Node38Domains1
    root5Node38Domains0Fast root5Node38Domains1Fast
    root5Node38Domains0_fast_eq root5Node38Domains1_fast_eq (by decide)
theorem root5Node38Step1_checked :
    checkReplacement table37 root5Node38Domains0 root5Node38Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node38Step1Chunk0_0_checked, root5Node38Step1Chunk0_1_checked, root5Node38Step1Chunk0_2_checked, root5Node38Step1Chunk0_3_checked, root5Node38Step1Chunk0_4_checked, root5Node38Step1Chunk0_5_checked, root5Node38Step1Chunk1_0_checked, root5Node38Step1Chunk1_1_checked, root5Node38Step1Chunk1_2_checked, root5Node38Step1Chunk1_3_checked, root5Node38Step1Chunk1_4_checked, root5Node38Step1Chunk1_5_checked, root5Node38Step1Chunk2_0_checked, root5Node38Step1Chunk2_1_checked, root5Node38Step1Chunk2_2_checked, root5Node38Step1Chunk2_3_checked, root5Node38Step1Chunk2_4_checked, root5Node38Step1Chunk2_5_checked, root5Node38Step1Chunk3_0_checked, root5Node38Step1Chunk3_1_checked, root5Node38Step1Chunk3_2_checked, root5Node38Step1Chunk3_3_checked, root5Node38Step1Chunk3_4_checked, root5Node38Step1Chunk3_5_checked, root5Node38Step1Chunk4_0_checked, root5Node38Step1Chunk4_1_checked, root5Node38Step1Chunk4_2_checked, root5Node38Step1Chunk4_3_checked, root5Node38Step1Chunk4_4_checked, root5Node38Step1Chunk4_5_checked, root5Node38Step1Chunk5_0_checked, root5Node38Step1Chunk5_1_checked, root5Node38Step1Chunk5_2_checked, root5Node38Step1Chunk5_3_checked, root5Node38Step1Chunk5_4_checked, root5Node38Step1Chunk5_5_checked, root5Node38Step1Chunk6_0_checked, root5Node38Step1Chunk6_1_checked, root5Node38Step1Chunk6_2_checked, root5Node38Step1Chunk6_3_checked, root5Node38Step1Chunk6_4_checked, root5Node38Step1Chunk6_5_checked, root5Node38Step1Chunk7_0_checked, root5Node38Step1Chunk7_1_checked, root5Node38Step1Chunk7_2_checked, root5Node38Step1Chunk7_3_checked, root5Node38Step1Chunk7_4_checked, root5Node38Step1Chunk7_5_checked, root5Node38Step1Chunk8_0_checked, root5Node38Step1Chunk8_1_checked, root5Node38Step1Chunk8_2_checked, root5Node38Step1Chunk8_3_checked, root5Node38Step1Chunk8_4_checked, root5Node38Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node38Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(0,1)]
  | 24 => [(6,2)]
  | 25 => [(8,4)]
  | 26 => [(1,2),(3,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
  | 50 => [(8,2)]
  | 51 => [(5,0)]
  | 52 => [(4,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(8,5)]
  | 56 => [(5,4)]
  | 57 => [(0,0)]
  | 58 => [(7,2)]
  | 59 => [(7,4)]
  | _ => [(6,3)]
def root5Node38Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(1,2),(3,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root5Node38Domains2_fast_eq : root5Node38Domains2 = expandDomains root5Node38Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node38Domains2 v = expandDomains root5Node38Domains2Fast v from by decide) v
theorem root5Node38Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root5Node38Domains1 root5Node38Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node38Domains1 root5Node38Domains2
    root5Node38Domains1Fast root5Node38Domains2Fast
    root5Node38Domains1_fast_eq root5Node38Domains2_fast_eq (by decide)
theorem root5Node38Step2_checked :
    checkReplacement table39 root5Node38Domains1 root5Node38Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node38Step2Chunk0_0_checked, root5Node38Step2Chunk0_1_checked, root5Node38Step2Chunk0_2_checked, root5Node38Step2Chunk0_3_checked, root5Node38Step2Chunk0_4_checked, root5Node38Step2Chunk0_5_checked, root5Node38Step2Chunk1_0_checked, root5Node38Step2Chunk1_1_checked, root5Node38Step2Chunk1_2_checked, root5Node38Step2Chunk1_3_checked, root5Node38Step2Chunk1_4_checked, root5Node38Step2Chunk1_5_checked, root5Node38Step2Chunk2_0_checked, root5Node38Step2Chunk2_1_checked, root5Node38Step2Chunk2_2_checked, root5Node38Step2Chunk2_3_checked, root5Node38Step2Chunk2_4_checked, root5Node38Step2Chunk2_5_checked, root5Node38Step2Chunk3_0_checked, root5Node38Step2Chunk3_1_checked, root5Node38Step2Chunk3_2_checked, root5Node38Step2Chunk3_3_checked, root5Node38Step2Chunk3_4_checked, root5Node38Step2Chunk3_5_checked, root5Node38Step2Chunk4_0_checked, root5Node38Step2Chunk4_1_checked, root5Node38Step2Chunk4_2_checked, root5Node38Step2Chunk4_3_checked, root5Node38Step2Chunk4_4_checked, root5Node38Step2Chunk4_5_checked, root5Node38Step2Chunk5_0_checked, root5Node38Step2Chunk5_1_checked, root5Node38Step2Chunk5_2_checked, root5Node38Step2Chunk5_3_checked, root5Node38Step2Chunk5_4_checked, root5Node38Step2Chunk5_5_checked, root5Node38Step2Chunk6_0_checked, root5Node38Step2Chunk6_1_checked, root5Node38Step2Chunk6_2_checked, root5Node38Step2Chunk6_3_checked, root5Node38Step2Chunk6_4_checked, root5Node38Step2Chunk6_5_checked, root5Node38Step2Chunk7_0_checked, root5Node38Step2Chunk7_1_checked, root5Node38Step2Chunk7_2_checked, root5Node38Step2Chunk7_3_checked, root5Node38Step2Chunk7_4_checked, root5Node38Step2Chunk7_5_checked, root5Node38Step2Chunk8_0_checked, root5Node38Step2Chunk8_1_checked, root5Node38Step2Chunk8_2_checked, root5Node38Step2Chunk8_3_checked, root5Node38Step2Chunk8_4_checked, root5Node38Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node39Domains0 : Domains 61 State := restrict root5Node38Domains2 26 (1,2)
def root5Node39Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(1,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root5Node39Domains0_fast_eq : root5Node39Domains0 = expandDomains root5Node39Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node39Domains0 v = expandDomains root5Node39Domains0Fast v from by decide) v
theorem root5Node39Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node39Domains0 (.output 18) = true := by decide
def root5Node40Domains0 : Domains 61 State := restrict root5Node38Domains2 26 (3,2)
def root5Node40Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(3,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
  | 50 => some [(8,2)]
  | 51 => some [(5,0)]
  | 52 => some [(4,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(8,5)]
  | 56 => some [(5,4)]
  | 57 => some [(0,0)]
  | 58 => some [(7,2)]
  | 59 => some [(7,4)]
  | _ => some [(6,3)]
theorem root5Node40Domains0_fast_eq : root5Node40Domains0 = expandDomains root5Node40Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node40Domains0 v = expandDomains root5Node40Domains0Fast v from by decide) v
theorem root5Node40Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node40Domains0 (.output 19) = true := by decide
def root5Node41Domains0 : Domains 61 State := restrict root5Node37Domains3 27 (8,0)
def root5Node41Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(1,2),(3,2),(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0)]
  | 42 => some [(7,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
  | 49 => some [(0,1)]
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
theorem root5Node41Domains0_fast_eq : root5Node41Domains0 = expandDomains root5Node41Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node41Domains0 v = expandDomains root5Node41Domains0Fast v from by decide) v
def root5Node41Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(6,4)]
  | 4 => [(1,2)]
  | 5 => [(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(0,3)]
  | 10 => [(4,1)]
  | 11 => [(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(2,2)]
  | 16 => [(3,3)]
  | 17 => [(5,2)]
  | 18 => [(0,2)]
  | 19 => [(1,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(0,1)]
  | 24 => [(6,2)]
  | 25 => [(8,4)]
  | 26 => [(5,2)]
  | 27 => [(8,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(5,4),(8,4)]
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
  | 52 => [(5,5),(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(1,4),(3,4),(7,4)]
  | 57 => [(0,5),(6,3)]
  | 58 => [(4,4),(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root5Node41Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(6,4)]
  | 4 => some [(1,2)]
  | 5 => some [(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3)]
  | 10 => some [(4,1)]
  | 11 => some [(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(2,2)]
  | 16 => some [(3,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2)]
  | 19 => some [(1,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(5,2)]
  | 27 => some [(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0)]
  | 33 => some [(7,1)]
  | 34 => some [(7,5)]
  | 35 => some [(5,4),(8,4)]
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
theorem root5Node41Domains1_fast_eq : root5Node41Domains1 = expandDomains root5Node41Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node41Domains1 v = expandDomains root5Node41Domains1Fast v from by decide) v
theorem root5Node41Step1Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root5Node41Domains0 root5Node41Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node41Domains0 root5Node41Domains1
    root5Node41Domains0Fast root5Node41Domains1Fast
    root5Node41Domains0_fast_eq root5Node41Domains1_fast_eq (by decide)
theorem root5Node41Step1_checked :
    checkReplacement table36 root5Node41Domains0 root5Node41Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node41Step1Chunk0_0_checked, root5Node41Step1Chunk0_1_checked, root5Node41Step1Chunk0_2_checked, root5Node41Step1Chunk0_3_checked, root5Node41Step1Chunk0_4_checked, root5Node41Step1Chunk0_5_checked, root5Node41Step1Chunk1_0_checked, root5Node41Step1Chunk1_1_checked, root5Node41Step1Chunk1_2_checked, root5Node41Step1Chunk1_3_checked, root5Node41Step1Chunk1_4_checked, root5Node41Step1Chunk1_5_checked, root5Node41Step1Chunk2_0_checked, root5Node41Step1Chunk2_1_checked, root5Node41Step1Chunk2_2_checked, root5Node41Step1Chunk2_3_checked, root5Node41Step1Chunk2_4_checked, root5Node41Step1Chunk2_5_checked, root5Node41Step1Chunk3_0_checked, root5Node41Step1Chunk3_1_checked, root5Node41Step1Chunk3_2_checked, root5Node41Step1Chunk3_3_checked, root5Node41Step1Chunk3_4_checked, root5Node41Step1Chunk3_5_checked, root5Node41Step1Chunk4_0_checked, root5Node41Step1Chunk4_1_checked, root5Node41Step1Chunk4_2_checked, root5Node41Step1Chunk4_3_checked, root5Node41Step1Chunk4_4_checked, root5Node41Step1Chunk4_5_checked, root5Node41Step1Chunk5_0_checked, root5Node41Step1Chunk5_1_checked, root5Node41Step1Chunk5_2_checked, root5Node41Step1Chunk5_3_checked, root5Node41Step1Chunk5_4_checked, root5Node41Step1Chunk5_5_checked, root5Node41Step1Chunk6_0_checked, root5Node41Step1Chunk6_1_checked, root5Node41Step1Chunk6_2_checked, root5Node41Step1Chunk6_3_checked, root5Node41Step1Chunk6_4_checked, root5Node41Step1Chunk6_5_checked, root5Node41Step1Chunk7_0_checked, root5Node41Step1Chunk7_1_checked, root5Node41Step1Chunk7_2_checked, root5Node41Step1Chunk7_3_checked, root5Node41Step1Chunk7_4_checked, root5Node41Step1Chunk7_5_checked, root5Node41Step1Chunk8_0_checked, root5Node41Step1Chunk8_1_checked, root5Node41Step1Chunk8_2_checked, root5Node41Step1Chunk8_3_checked, root5Node41Step1Chunk8_4_checked, root5Node41Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
