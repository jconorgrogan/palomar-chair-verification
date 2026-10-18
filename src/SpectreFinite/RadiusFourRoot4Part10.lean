module

public import SpectreFinite.RadiusFourRoot4Part9
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable1
public import SpectreFinite.RadiusFourTable19
public import SpectreFinite.RadiusFourTable26
public import SpectreFinite.RadiusFourTable31
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root4Node27Domains0 : Domains 61 State := restrict root4Node26Domains3 2 (4,1)
def root4Node27Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(1,1),(7,1)]
  | 5 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 6 => some [(2,0),(2,2),(4,0)]
  | 7 => some [(3,3),(7,3)]
  | 8 => some [(5,2),(8,2)]
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
theorem root4Node27Domains0_fast_eq : root4Node27Domains0 = expandDomains root4Node27Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node27Domains0 v = expandDomains root4Node27Domains0Fast v from by decide) v
def root4Node27Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(7,5)]
  | 1 => [(0,3),(1,1),(6,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(0,5),(1,2),(3,2),(6,3)]
  | 6 => [(2,0),(2,2),(4,0)]
  | 7 => [(3,3),(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3),(8,3)]
  | 11 => [(0,2),(0,3),(6,0),(6,1)]
  | 12 => [(1,1),(3,1),(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(4,2),(5,2),(7,0),(8,2)]
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
def root4Node27Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5),(1,2),(3,2),(6,3)]
  | 6 => some [(2,0),(2,2),(4,0)]
  | 7 => some [(3,3),(7,3)]
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
theorem root4Node27Domains1_fast_eq : root4Node27Domains1 = expandDomains root4Node27Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node27Domains1 v = expandDomains root4Node27Domains1Fast v from by decide) v
theorem root4Node27Step1Chunk0_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk0_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk0_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk0_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk0_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk0_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows0_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk1_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows1_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk2_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows2_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk3_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows3_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk4_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows4_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk5_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows5_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk6_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows6_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk7_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows7_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_0_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_0⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_1_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_1⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_2_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_2⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_3_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_3⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_4_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_4⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1Chunk8_5_checked :
    checkNarrowing ⟨table1Scope, table1Rows8_5⟩
      root4Node27Domains0 root4Node27Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node27Domains0 root4Node27Domains1
    root4Node27Domains0Fast root4Node27Domains1Fast
    root4Node27Domains0_fast_eq root4Node27Domains1_fast_eq (by decide)
theorem root4Node27Step1_checked :
    checkReplacement table1 root4Node27Domains0 root4Node27Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node27Step1Chunk0_0_checked, root4Node27Step1Chunk0_1_checked, root4Node27Step1Chunk0_2_checked, root4Node27Step1Chunk0_3_checked, root4Node27Step1Chunk0_4_checked, root4Node27Step1Chunk0_5_checked, root4Node27Step1Chunk1_0_checked, root4Node27Step1Chunk1_1_checked, root4Node27Step1Chunk1_2_checked, root4Node27Step1Chunk1_3_checked, root4Node27Step1Chunk1_4_checked, root4Node27Step1Chunk1_5_checked, root4Node27Step1Chunk2_0_checked, root4Node27Step1Chunk2_1_checked, root4Node27Step1Chunk2_2_checked, root4Node27Step1Chunk2_3_checked, root4Node27Step1Chunk2_4_checked, root4Node27Step1Chunk2_5_checked, root4Node27Step1Chunk3_0_checked, root4Node27Step1Chunk3_1_checked, root4Node27Step1Chunk3_2_checked, root4Node27Step1Chunk3_3_checked, root4Node27Step1Chunk3_4_checked, root4Node27Step1Chunk3_5_checked, root4Node27Step1Chunk4_0_checked, root4Node27Step1Chunk4_1_checked, root4Node27Step1Chunk4_2_checked, root4Node27Step1Chunk4_3_checked, root4Node27Step1Chunk4_4_checked, root4Node27Step1Chunk4_5_checked, root4Node27Step1Chunk5_0_checked, root4Node27Step1Chunk5_1_checked, root4Node27Step1Chunk5_2_checked, root4Node27Step1Chunk5_3_checked, root4Node27Step1Chunk5_4_checked, root4Node27Step1Chunk5_5_checked, root4Node27Step1Chunk6_0_checked, root4Node27Step1Chunk6_1_checked, root4Node27Step1Chunk6_2_checked, root4Node27Step1Chunk6_3_checked, root4Node27Step1Chunk6_4_checked, root4Node27Step1Chunk6_5_checked, root4Node27Step1Chunk7_0_checked, root4Node27Step1Chunk7_1_checked, root4Node27Step1Chunk7_2_checked, root4Node27Step1Chunk7_3_checked, root4Node27Step1Chunk7_4_checked, root4Node27Step1Chunk7_5_checked, root4Node27Step1Chunk8_0_checked, root4Node27Step1Chunk8_1_checked, root4Node27Step1Chunk8_2_checked, root4Node27Step1Chunk8_3_checked, root4Node27Step1Chunk8_4_checked, root4Node27Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node28Domains0 : Domains 61 State := restrict root4Node27Domains1 7 (3,3)
def root4Node28Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(0,5),(1,2),(3,2),(6,3)]
  | 6 => some [(2,0),(2,2),(4,0)]
  | 7 => some [(3,3)]
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
theorem root4Node28Domains0_fast_eq : root4Node28Domains0 = expandDomains root4Node28Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node28Domains0 v = expandDomains root4Node28Domains0Fast v from by decide) v
def root4Node28Domains1 (v : Fin 61) : List State :=
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
  | 10 => [(7,3),(8,3)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(5,2)]
  | 19 => [(5,0)]
  | 20 => [(4,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(7,1),(8,1)]
  | 26 => [(1,2),(6,2)]
  | 27 => [(8,4)]
  | 28 => [(0,0)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => [(4,5),(7,3),(8,5)]
  | 35 => [(7,1),(8,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(6,3),(6,4)]
  | 43 => [(4,5),(5,5),(8,5)]
  | 44 => [(7,0)]
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
def root4Node28Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 10 => some [(7,3),(8,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(5,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,5)]
  | 35 => some [(7,1),(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3),(6,4)]
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(7,0)]
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
theorem root4Node28Domains1_fast_eq : root4Node28Domains1 = expandDomains root4Node28Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node28Domains1 v = expandDomains root4Node28Domains1Fast v from by decide) v
theorem root4Node28Step1Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root4Node28Domains0 root4Node28Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains0 root4Node28Domains1
    root4Node28Domains0Fast root4Node28Domains1Fast
    root4Node28Domains0_fast_eq root4Node28Domains1_fast_eq (by decide)
theorem root4Node28Step1_checked :
    checkReplacement table19 root4Node28Domains0 root4Node28Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node28Step1Chunk0_0_checked, root4Node28Step1Chunk0_1_checked, root4Node28Step1Chunk0_2_checked, root4Node28Step1Chunk0_3_checked, root4Node28Step1Chunk0_4_checked, root4Node28Step1Chunk0_5_checked, root4Node28Step1Chunk1_0_checked, root4Node28Step1Chunk1_1_checked, root4Node28Step1Chunk1_2_checked, root4Node28Step1Chunk1_3_checked, root4Node28Step1Chunk1_4_checked, root4Node28Step1Chunk1_5_checked, root4Node28Step1Chunk2_0_checked, root4Node28Step1Chunk2_1_checked, root4Node28Step1Chunk2_2_checked, root4Node28Step1Chunk2_3_checked, root4Node28Step1Chunk2_4_checked, root4Node28Step1Chunk2_5_checked, root4Node28Step1Chunk3_0_checked, root4Node28Step1Chunk3_1_checked, root4Node28Step1Chunk3_2_checked, root4Node28Step1Chunk3_3_checked, root4Node28Step1Chunk3_4_checked, root4Node28Step1Chunk3_5_checked, root4Node28Step1Chunk4_0_checked, root4Node28Step1Chunk4_1_checked, root4Node28Step1Chunk4_2_checked, root4Node28Step1Chunk4_3_checked, root4Node28Step1Chunk4_4_checked, root4Node28Step1Chunk4_5_checked, root4Node28Step1Chunk5_0_checked, root4Node28Step1Chunk5_1_checked, root4Node28Step1Chunk5_2_checked, root4Node28Step1Chunk5_3_checked, root4Node28Step1Chunk5_4_checked, root4Node28Step1Chunk5_5_checked, root4Node28Step1Chunk6_0_checked, root4Node28Step1Chunk6_1_checked, root4Node28Step1Chunk6_2_checked, root4Node28Step1Chunk6_3_checked, root4Node28Step1Chunk6_4_checked, root4Node28Step1Chunk6_5_checked, root4Node28Step1Chunk7_0_checked, root4Node28Step1Chunk7_1_checked, root4Node28Step1Chunk7_2_checked, root4Node28Step1Chunk7_3_checked, root4Node28Step1Chunk7_4_checked, root4Node28Step1Chunk7_5_checked, root4Node28Step1Chunk8_0_checked, root4Node28Step1Chunk8_1_checked, root4Node28Step1Chunk8_2_checked, root4Node28Step1Chunk8_3_checked, root4Node28Step1Chunk8_4_checked, root4Node28Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node28Domains2 (v : Fin 61) : List State :=
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
  | 10 => [(7,3),(8,3)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4),(6,4)]
  | 17 => [(0,5),(1,2)]
  | 18 => [(5,2)]
  | 19 => [(5,0)]
  | 20 => [(4,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3),(6,0)]
  | 25 => [(7,1),(8,1)]
  | 26 => [(1,2),(6,2)]
  | 27 => [(8,4)]
  | 28 => [(0,0)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2),(8,2)]
  | 33 => [(5,0),(5,3),(8,0)]
  | 34 => [(4,5),(7,3),(8,5)]
  | 35 => [(7,1),(8,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(6,3),(6,4)]
  | 43 => [(4,5),(5,5),(8,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(5,5),(8,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1),(7,1)]
  | 49 => [(0,2),(1,5),(7,5)]
  | 50 => [(4,4),(7,2)]
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
def root4Node28Domains2Fast (v : Fin 61) : Option (List State) :=
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
  | 10 => some [(7,3),(8,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(5,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,5)]
  | 35 => some [(7,1),(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3),(6,4)]
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(4,4),(7,2)]
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
theorem root4Node28Domains2_fast_eq : root4Node28Domains2 = expandDomains root4Node28Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node28Domains2 v = expandDomains root4Node28Domains2Fast v from by decide) v
theorem root4Node28Step2Chunk0_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_0⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk0_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_1⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk0_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_2⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk0_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_3⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk0_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_4⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk0_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows0_5⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk1_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_0⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk1_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_1⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk1_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_2⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk1_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_3⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk1_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_4⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk1_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows1_5⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk2_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_0⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk2_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_1⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk2_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_2⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk2_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_3⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk2_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_4⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk2_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows2_5⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk3_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_0⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk3_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_1⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk3_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_2⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk3_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_3⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk3_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_4⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk3_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows3_5⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk4_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_0⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk4_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_1⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk4_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_2⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk4_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_3⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk4_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_4⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk4_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows4_5⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk5_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_0⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk5_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_1⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk5_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_2⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk5_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_3⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk5_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_4⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk5_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows5_5⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk6_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_0⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk6_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_1⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk6_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_2⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk6_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_3⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk6_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_4⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk6_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows6_5⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk7_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_0⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk7_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_1⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk7_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_2⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk7_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_3⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk7_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_4⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk7_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows7_5⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk8_0_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_0⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk8_1_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_1⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk8_2_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_2⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk8_3_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_3⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk8_4_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_4⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2Chunk8_5_checked :
    checkNarrowing ⟨table26Scope, table26Rows8_5⟩
      root4Node28Domains1 root4Node28Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node28Domains1 root4Node28Domains2
    root4Node28Domains1Fast root4Node28Domains2Fast
    root4Node28Domains1_fast_eq root4Node28Domains2_fast_eq (by decide)
theorem root4Node28Step2_checked :
    checkReplacement table26 root4Node28Domains1 root4Node28Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node28Step2Chunk0_0_checked, root4Node28Step2Chunk0_1_checked, root4Node28Step2Chunk0_2_checked, root4Node28Step2Chunk0_3_checked, root4Node28Step2Chunk0_4_checked, root4Node28Step2Chunk0_5_checked, root4Node28Step2Chunk1_0_checked, root4Node28Step2Chunk1_1_checked, root4Node28Step2Chunk1_2_checked, root4Node28Step2Chunk1_3_checked, root4Node28Step2Chunk1_4_checked, root4Node28Step2Chunk1_5_checked, root4Node28Step2Chunk2_0_checked, root4Node28Step2Chunk2_1_checked, root4Node28Step2Chunk2_2_checked, root4Node28Step2Chunk2_3_checked, root4Node28Step2Chunk2_4_checked, root4Node28Step2Chunk2_5_checked, root4Node28Step2Chunk3_0_checked, root4Node28Step2Chunk3_1_checked, root4Node28Step2Chunk3_2_checked, root4Node28Step2Chunk3_3_checked, root4Node28Step2Chunk3_4_checked, root4Node28Step2Chunk3_5_checked, root4Node28Step2Chunk4_0_checked, root4Node28Step2Chunk4_1_checked, root4Node28Step2Chunk4_2_checked, root4Node28Step2Chunk4_3_checked, root4Node28Step2Chunk4_4_checked, root4Node28Step2Chunk4_5_checked, root4Node28Step2Chunk5_0_checked, root4Node28Step2Chunk5_1_checked, root4Node28Step2Chunk5_2_checked, root4Node28Step2Chunk5_3_checked, root4Node28Step2Chunk5_4_checked, root4Node28Step2Chunk5_5_checked, root4Node28Step2Chunk6_0_checked, root4Node28Step2Chunk6_1_checked, root4Node28Step2Chunk6_2_checked, root4Node28Step2Chunk6_3_checked, root4Node28Step2Chunk6_4_checked, root4Node28Step2Chunk6_5_checked, root4Node28Step2Chunk7_0_checked, root4Node28Step2Chunk7_1_checked, root4Node28Step2Chunk7_2_checked, root4Node28Step2Chunk7_3_checked, root4Node28Step2Chunk7_4_checked, root4Node28Step2Chunk7_5_checked, root4Node28Step2Chunk8_0_checked, root4Node28Step2Chunk8_1_checked, root4Node28Step2Chunk8_2_checked, root4Node28Step2Chunk8_3_checked, root4Node28Step2Chunk8_4_checked, root4Node28Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node29Domains0 : Domains 61 State := restrict root4Node28Domains2 10 (7,3)
def root4Node29Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 10 => some [(7,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(5,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3),(8,0)]
  | 34 => some [(4,5),(7,3),(8,5)]
  | 35 => some [(7,1),(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3),(6,4)]
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5),(8,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1),(7,1)]
  | 49 => some [(0,2),(1,5),(7,5)]
  | 50 => some [(4,4),(7,2)]
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
theorem root4Node29Domains0_fast_eq : root4Node29Domains0 = expandDomains root4Node29Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node29Domains0 v = expandDomains root4Node29Domains0Fast v from by decide) v
def root4Node29Domains1 (v : Fin 61) : List State :=
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
  | 10 => [(7,3)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(5,2)]
  | 19 => [(5,0)]
  | 20 => [(4,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(8,1)]
  | 26 => [(1,2),(6,2)]
  | 27 => [(8,4)]
  | 28 => [(0,0)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(7,1),(8,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(4,5),(5,5),(8,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(5,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4),(7,2)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(3,2)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(1,5),(5,1),(5,4)]
  | _ => [(0,0),(0,1),(6,1),(6,4)]
def root4Node29Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 10 => some [(7,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(5,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(1,2),(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(7,1),(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(3,2)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(1,5),(5,1),(5,4)]
  | _ => some [(0,0),(0,1),(6,1),(6,4)]
theorem root4Node29Domains1_fast_eq : root4Node29Domains1 = expandDomains root4Node29Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node29Domains1 v = expandDomains root4Node29Domains1Fast v from by decide) v
theorem root4Node29Step1Chunk0_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk0_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk0_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk0_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk0_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk0_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk1_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk2_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk3_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk4_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk5_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk6_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk7_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_0⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_1⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_2⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_3⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_4⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1Chunk8_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_5⟩
      root4Node29Domains0 root4Node29Domains1 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains0 root4Node29Domains1
    root4Node29Domains0Fast root4Node29Domains1Fast
    root4Node29Domains0_fast_eq root4Node29Domains1_fast_eq (by decide)
theorem root4Node29Step1_checked :
    checkReplacement table31 root4Node29Domains0 root4Node29Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node29Step1Chunk0_0_checked, root4Node29Step1Chunk0_1_checked, root4Node29Step1Chunk0_2_checked, root4Node29Step1Chunk0_3_checked, root4Node29Step1Chunk0_4_checked, root4Node29Step1Chunk0_5_checked, root4Node29Step1Chunk1_0_checked, root4Node29Step1Chunk1_1_checked, root4Node29Step1Chunk1_2_checked, root4Node29Step1Chunk1_3_checked, root4Node29Step1Chunk1_4_checked, root4Node29Step1Chunk1_5_checked, root4Node29Step1Chunk2_0_checked, root4Node29Step1Chunk2_1_checked, root4Node29Step1Chunk2_2_checked, root4Node29Step1Chunk2_3_checked, root4Node29Step1Chunk2_4_checked, root4Node29Step1Chunk2_5_checked, root4Node29Step1Chunk3_0_checked, root4Node29Step1Chunk3_1_checked, root4Node29Step1Chunk3_2_checked, root4Node29Step1Chunk3_3_checked, root4Node29Step1Chunk3_4_checked, root4Node29Step1Chunk3_5_checked, root4Node29Step1Chunk4_0_checked, root4Node29Step1Chunk4_1_checked, root4Node29Step1Chunk4_2_checked, root4Node29Step1Chunk4_3_checked, root4Node29Step1Chunk4_4_checked, root4Node29Step1Chunk4_5_checked, root4Node29Step1Chunk5_0_checked, root4Node29Step1Chunk5_1_checked, root4Node29Step1Chunk5_2_checked, root4Node29Step1Chunk5_3_checked, root4Node29Step1Chunk5_4_checked, root4Node29Step1Chunk5_5_checked, root4Node29Step1Chunk6_0_checked, root4Node29Step1Chunk6_1_checked, root4Node29Step1Chunk6_2_checked, root4Node29Step1Chunk6_3_checked, root4Node29Step1Chunk6_4_checked, root4Node29Step1Chunk6_5_checked, root4Node29Step1Chunk7_0_checked, root4Node29Step1Chunk7_1_checked, root4Node29Step1Chunk7_2_checked, root4Node29Step1Chunk7_3_checked, root4Node29Step1Chunk7_4_checked, root4Node29Step1Chunk7_5_checked, root4Node29Step1Chunk8_0_checked, root4Node29Step1Chunk8_1_checked, root4Node29Step1Chunk8_2_checked, root4Node29Step1Chunk8_3_checked, root4Node29Step1Chunk8_4_checked, root4Node29Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root4Node29Domains2 (v : Fin 61) : List State :=
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
  | 10 => [(7,3)]
  | 11 => [(0,2)]
  | 12 => [(1,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(5,2)]
  | 19 => [(5,0)]
  | 20 => [(4,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(8,1)]
  | 26 => [(1,2),(6,2)]
  | 27 => [(8,4)]
  | 28 => [(0,0)]
  | 29 => [(7,2)]
  | 30 => [(4,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(7,1),(8,1)]
  | 36 => [(1,5)]
  | 37 => [(6,1)]
  | 38 => [(5,1)]
  | 39 => [(0,1)]
  | 40 => [(6,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(8,3)]
  | 46 => [(5,5)]
  | 47 => [(1,0)]
  | 48 => [(2,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(4,4)]
  | 54 => [(0,0)]
  | 55 => [(3,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(7,1)]
  | 59 => [(1,5)]
  | _ => [(6,1)]
def root4Node29Domains2Fast (v : Fin 61) : Option (List State) :=
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
  | 10 => some [(7,3)]
  | 11 => some [(0,2)]
  | 12 => some [(1,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(5,2)]
  | 19 => some [(5,0)]
  | 20 => some [(4,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(1,2),(6,2)]
  | 27 => some [(8,4)]
  | 28 => some [(0,0)]
  | 29 => some [(7,2)]
  | 30 => some [(4,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(7,1),(8,1)]
  | 36 => some [(1,5)]
  | 37 => some [(6,1)]
  | 38 => some [(5,1)]
  | 39 => some [(0,1)]
  | 40 => some [(6,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(8,3)]
  | 46 => some [(5,5)]
  | 47 => some [(1,0)]
  | 48 => some [(2,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(4,4)]
  | 54 => some [(0,0)]
  | 55 => some [(3,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(7,1)]
  | 59 => some [(1,5)]
  | _ => some [(6,1)]
theorem root4Node29Domains2_fast_eq : root4Node29Domains2 = expandDomains root4Node29Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root4Node29Domains2 v = expandDomains root4Node29Domains2Fast v from by decide) v
theorem root4Node29Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root4Node29Domains1 root4Node29Domains2 = true := by
  exact checkNarrowing_of_fast _ root4Node29Domains1 root4Node29Domains2
    root4Node29Domains1Fast root4Node29Domains2Fast
    root4Node29Domains1_fast_eq root4Node29Domains2_fast_eq (by decide)
theorem root4Node29Step2_checked :
    checkReplacement table46 root4Node29Domains1 root4Node29Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root4Node29Step2Chunk0_0_checked, root4Node29Step2Chunk0_1_checked, root4Node29Step2Chunk0_2_checked, root4Node29Step2Chunk0_3_checked, root4Node29Step2Chunk0_4_checked, root4Node29Step2Chunk0_5_checked, root4Node29Step2Chunk1_0_checked, root4Node29Step2Chunk1_1_checked, root4Node29Step2Chunk1_2_checked, root4Node29Step2Chunk1_3_checked, root4Node29Step2Chunk1_4_checked, root4Node29Step2Chunk1_5_checked, root4Node29Step2Chunk2_0_checked, root4Node29Step2Chunk2_1_checked, root4Node29Step2Chunk2_2_checked, root4Node29Step2Chunk2_3_checked, root4Node29Step2Chunk2_4_checked, root4Node29Step2Chunk2_5_checked, root4Node29Step2Chunk3_0_checked, root4Node29Step2Chunk3_1_checked, root4Node29Step2Chunk3_2_checked, root4Node29Step2Chunk3_3_checked, root4Node29Step2Chunk3_4_checked, root4Node29Step2Chunk3_5_checked, root4Node29Step2Chunk4_0_checked, root4Node29Step2Chunk4_1_checked, root4Node29Step2Chunk4_2_checked, root4Node29Step2Chunk4_3_checked, root4Node29Step2Chunk4_4_checked, root4Node29Step2Chunk4_5_checked, root4Node29Step2Chunk5_0_checked, root4Node29Step2Chunk5_1_checked, root4Node29Step2Chunk5_2_checked, root4Node29Step2Chunk5_3_checked, root4Node29Step2Chunk5_4_checked, root4Node29Step2Chunk5_5_checked, root4Node29Step2Chunk6_0_checked, root4Node29Step2Chunk6_1_checked, root4Node29Step2Chunk6_2_checked, root4Node29Step2Chunk6_3_checked, root4Node29Step2Chunk6_4_checked, root4Node29Step2Chunk6_5_checked, root4Node29Step2Chunk7_0_checked, root4Node29Step2Chunk7_1_checked, root4Node29Step2Chunk7_2_checked, root4Node29Step2Chunk7_3_checked, root4Node29Step2Chunk7_4_checked, root4Node29Step2Chunk7_5_checked, root4Node29Step2Chunk8_0_checked, root4Node29Step2Chunk8_1_checked, root4Node29Step2Chunk8_2_checked, root4Node29Step2Chunk8_3_checked, root4Node29Step2Chunk8_4_checked, root4Node29Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
