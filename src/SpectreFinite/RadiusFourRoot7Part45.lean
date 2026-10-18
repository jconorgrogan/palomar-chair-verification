module

public import SpectreFinite.RadiusFourRoot7Part44
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable22
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node137Domains0 : Domains 61 State := restrict root7Node136Domains3 3 (1,4)
def root7Node137Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5),(1,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(0,3),(6,0)]
  | 10 => some [(7,1),(8,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2),(8,2)]
  | 16 => some [(5,0),(5,3),(8,0)]
  | 17 => some [(4,5),(7,3),(8,5)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(3,4),(5,4)]
  | 24 => some [(0,0),(6,3),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(8,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3),(4,3)]
  | 32 => some [(0,2),(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(1,1),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(5,4),(7,2),(8,4)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(6,4),(7,4)]
  | 40 => some [(0,5),(1,2),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(0,3),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(5,2),(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5),(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(6,3),(6,4)]
theorem root7Node137Domains0_fast_eq : root7Node137Domains0 = expandDomains root7Node137Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node137Domains0 v = expandDomains root7Node137Domains0Fast v from by decide) v
def root7Node137Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(0,0),(6,4)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(4,5),(5,2),(5,5),(8,5)]
  | 27 => [(7,0),(8,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(1,5),(3,5),(7,5)]
  | 33 => [(0,3),(6,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(4,4),(5,4),(7,2),(8,4)]
  | 36 => [(1,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,2)]
  | 42 => [(1,3),(3,3),(5,3),(7,3)]
  | 43 => [(4,1),(7,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(6,5)]
  | 50 => [(5,2),(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(4,2),(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(5,3),(7,0)]
  | 55 => [(2,3),(2,5),(4,5),(8,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(1,4),(6,4)]
  | 58 => [(0,5),(1,2)]
  | 59 => [(4,4),(7,4),(8,4)]
  | _ => [(0,0),(1,3),(6,3),(6,4)]
def root7Node137Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,2),(5,5),(8,5)]
  | 27 => some [(7,0),(8,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(5,4),(7,2),(8,4)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(5,2),(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5),(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(6,3),(6,4)]
theorem root7Node137Domains1_fast_eq : root7Node137Domains1 = expandDomains root7Node137Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node137Domains1 v = expandDomains root7Node137Domains1Fast v from by decide) v
theorem root7Node137Step1Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root7Node137Domains0 root7Node137Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains0 root7Node137Domains1
    root7Node137Domains0Fast root7Node137Domains1Fast
    root7Node137Domains0_fast_eq root7Node137Domains1_fast_eq (by decide)
theorem root7Node137Step1_checked :
    checkReplacement table22 root7Node137Domains0 root7Node137Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node137Step1Chunk0_0_checked, root7Node137Step1Chunk0_1_checked, root7Node137Step1Chunk0_2_checked, root7Node137Step1Chunk0_3_checked, root7Node137Step1Chunk0_4_checked, root7Node137Step1Chunk0_5_checked, root7Node137Step1Chunk1_0_checked, root7Node137Step1Chunk1_1_checked, root7Node137Step1Chunk1_2_checked, root7Node137Step1Chunk1_3_checked, root7Node137Step1Chunk1_4_checked, root7Node137Step1Chunk1_5_checked, root7Node137Step1Chunk2_0_checked, root7Node137Step1Chunk2_1_checked, root7Node137Step1Chunk2_2_checked, root7Node137Step1Chunk2_3_checked, root7Node137Step1Chunk2_4_checked, root7Node137Step1Chunk2_5_checked, root7Node137Step1Chunk3_0_checked, root7Node137Step1Chunk3_1_checked, root7Node137Step1Chunk3_2_checked, root7Node137Step1Chunk3_3_checked, root7Node137Step1Chunk3_4_checked, root7Node137Step1Chunk3_5_checked, root7Node137Step1Chunk4_0_checked, root7Node137Step1Chunk4_1_checked, root7Node137Step1Chunk4_2_checked, root7Node137Step1Chunk4_3_checked, root7Node137Step1Chunk4_4_checked, root7Node137Step1Chunk4_5_checked, root7Node137Step1Chunk5_0_checked, root7Node137Step1Chunk5_1_checked, root7Node137Step1Chunk5_2_checked, root7Node137Step1Chunk5_3_checked, root7Node137Step1Chunk5_4_checked, root7Node137Step1Chunk5_5_checked, root7Node137Step1Chunk6_0_checked, root7Node137Step1Chunk6_1_checked, root7Node137Step1Chunk6_2_checked, root7Node137Step1Chunk6_3_checked, root7Node137Step1Chunk6_4_checked, root7Node137Step1Chunk6_5_checked, root7Node137Step1Chunk7_0_checked, root7Node137Step1Chunk7_1_checked, root7Node137Step1Chunk7_2_checked, root7Node137Step1Chunk7_3_checked, root7Node137Step1Chunk7_4_checked, root7Node137Step1Chunk7_5_checked, root7Node137Step1Chunk8_0_checked, root7Node137Step1Chunk8_1_checked, root7Node137Step1Chunk8_2_checked, root7Node137Step1Chunk8_3_checked, root7Node137Step1Chunk8_4_checked, root7Node137Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node137Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(0,0),(6,4)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(4,5),(5,5),(8,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(1,5),(3,5),(7,5)]
  | 33 => [(0,3),(6,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(4,4),(7,2)]
  | 36 => [(1,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,2)]
  | 42 => [(1,3),(3,3),(5,3),(7,3)]
  | 43 => [(4,1),(7,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(6,5)]
  | 50 => [(5,2),(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(5,3),(7,0)]
  | 55 => [(2,3),(2,5),(4,5),(8,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(1,4),(6,4)]
  | 58 => [(0,5),(1,2)]
  | 59 => [(4,4),(7,4),(8,4)]
  | _ => [(0,0),(1,3),(6,3),(6,4)]
def root7Node137Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,5),(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(7,2)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(5,2),(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5),(8,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(6,3),(6,4)]
theorem root7Node137Domains2_fast_eq : root7Node137Domains2 = expandDomains root7Node137Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node137Domains2 v = expandDomains root7Node137Domains2Fast v from by decide) v
theorem root7Node137Step2Chunk0_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_0⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk0_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_1⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk0_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_2⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk0_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_3⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk0_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_4⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk0_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_5⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk1_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_0⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk1_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_1⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk1_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_2⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk1_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_3⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk1_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_4⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk1_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_5⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk2_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_0⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk2_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_1⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk2_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_2⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk2_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_3⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk2_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_4⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk2_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_5⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk3_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_0⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk3_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_1⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk3_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_2⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk3_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_3⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk3_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_4⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk3_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows3_5⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk4_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_0⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk4_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_1⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk4_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_2⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk4_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_3⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk4_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_4⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk4_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows4_5⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk5_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_0⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk5_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_1⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk5_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_2⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk5_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_3⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk5_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_4⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk5_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows5_5⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk6_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_0⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk6_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_1⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk6_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_2⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk6_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_3⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk6_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_4⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk6_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows6_5⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk7_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_0⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk7_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_1⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk7_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_2⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk7_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_3⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk7_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_4⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk7_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows7_5⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk8_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_0⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk8_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_1⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk8_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_2⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk8_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_3⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk8_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_4⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2Chunk8_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows8_5⟩
      root7Node137Domains1 root7Node137Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains1 root7Node137Domains2
    root7Node137Domains1Fast root7Node137Domains2Fast
    root7Node137Domains1_fast_eq root7Node137Domains2_fast_eq (by decide)
theorem root7Node137Step2_checked :
    checkReplacement table29 root7Node137Domains1 root7Node137Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node137Step2Chunk0_0_checked, root7Node137Step2Chunk0_1_checked, root7Node137Step2Chunk0_2_checked, root7Node137Step2Chunk0_3_checked, root7Node137Step2Chunk0_4_checked, root7Node137Step2Chunk0_5_checked, root7Node137Step2Chunk1_0_checked, root7Node137Step2Chunk1_1_checked, root7Node137Step2Chunk1_2_checked, root7Node137Step2Chunk1_3_checked, root7Node137Step2Chunk1_4_checked, root7Node137Step2Chunk1_5_checked, root7Node137Step2Chunk2_0_checked, root7Node137Step2Chunk2_1_checked, root7Node137Step2Chunk2_2_checked, root7Node137Step2Chunk2_3_checked, root7Node137Step2Chunk2_4_checked, root7Node137Step2Chunk2_5_checked, root7Node137Step2Chunk3_0_checked, root7Node137Step2Chunk3_1_checked, root7Node137Step2Chunk3_2_checked, root7Node137Step2Chunk3_3_checked, root7Node137Step2Chunk3_4_checked, root7Node137Step2Chunk3_5_checked, root7Node137Step2Chunk4_0_checked, root7Node137Step2Chunk4_1_checked, root7Node137Step2Chunk4_2_checked, root7Node137Step2Chunk4_3_checked, root7Node137Step2Chunk4_4_checked, root7Node137Step2Chunk4_5_checked, root7Node137Step2Chunk5_0_checked, root7Node137Step2Chunk5_1_checked, root7Node137Step2Chunk5_2_checked, root7Node137Step2Chunk5_3_checked, root7Node137Step2Chunk5_4_checked, root7Node137Step2Chunk5_5_checked, root7Node137Step2Chunk6_0_checked, root7Node137Step2Chunk6_1_checked, root7Node137Step2Chunk6_2_checked, root7Node137Step2Chunk6_3_checked, root7Node137Step2Chunk6_4_checked, root7Node137Step2Chunk6_5_checked, root7Node137Step2Chunk7_0_checked, root7Node137Step2Chunk7_1_checked, root7Node137Step2Chunk7_2_checked, root7Node137Step2Chunk7_3_checked, root7Node137Step2Chunk7_4_checked, root7Node137Step2Chunk7_5_checked, root7Node137Step2Chunk8_0_checked, root7Node137Step2Chunk8_1_checked, root7Node137Step2Chunk8_2_checked, root7Node137Step2Chunk8_3_checked, root7Node137Step2Chunk8_4_checked, root7Node137Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node137Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(0,0),(6,4)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(4,5),(5,5),(8,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(1,5),(3,5),(7,5)]
  | 33 => [(0,3),(6,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(4,4),(7,2)]
  | 36 => [(1,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,2)]
  | 42 => [(1,3),(3,3),(5,3),(7,3)]
  | 43 => [(4,1),(7,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(6,5)]
  | 50 => [(5,2),(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(7,0)]
  | 55 => [(2,3),(2,5),(4,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(1,4),(6,4)]
  | 58 => [(0,5),(1,2)]
  | 59 => [(4,4),(8,4)]
  | _ => [(0,0),(6,4)]
def root7Node137Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,5),(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(7,2)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(5,2),(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node137Domains3_fast_eq : root7Node137Domains3 = expandDomains root7Node137Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node137Domains3 v = expandDomains root7Node137Domains3Fast v from by decide) v
theorem root7Node137Step3Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node137Domains2 root7Node137Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains2 root7Node137Domains3
    root7Node137Domains2Fast root7Node137Domains3Fast
    root7Node137Domains2_fast_eq root7Node137Domains3_fast_eq (by decide)
theorem root7Node137Step3_checked :
    checkReplacement table39 root7Node137Domains2 root7Node137Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node137Step3Chunk0_0_checked, root7Node137Step3Chunk0_1_checked, root7Node137Step3Chunk0_2_checked, root7Node137Step3Chunk0_3_checked, root7Node137Step3Chunk0_4_checked, root7Node137Step3Chunk0_5_checked, root7Node137Step3Chunk1_0_checked, root7Node137Step3Chunk1_1_checked, root7Node137Step3Chunk1_2_checked, root7Node137Step3Chunk1_3_checked, root7Node137Step3Chunk1_4_checked, root7Node137Step3Chunk1_5_checked, root7Node137Step3Chunk2_0_checked, root7Node137Step3Chunk2_1_checked, root7Node137Step3Chunk2_2_checked, root7Node137Step3Chunk2_3_checked, root7Node137Step3Chunk2_4_checked, root7Node137Step3Chunk2_5_checked, root7Node137Step3Chunk3_0_checked, root7Node137Step3Chunk3_1_checked, root7Node137Step3Chunk3_2_checked, root7Node137Step3Chunk3_3_checked, root7Node137Step3Chunk3_4_checked, root7Node137Step3Chunk3_5_checked, root7Node137Step3Chunk4_0_checked, root7Node137Step3Chunk4_1_checked, root7Node137Step3Chunk4_2_checked, root7Node137Step3Chunk4_3_checked, root7Node137Step3Chunk4_4_checked, root7Node137Step3Chunk4_5_checked, root7Node137Step3Chunk5_0_checked, root7Node137Step3Chunk5_1_checked, root7Node137Step3Chunk5_2_checked, root7Node137Step3Chunk5_3_checked, root7Node137Step3Chunk5_4_checked, root7Node137Step3Chunk5_5_checked, root7Node137Step3Chunk6_0_checked, root7Node137Step3Chunk6_1_checked, root7Node137Step3Chunk6_2_checked, root7Node137Step3Chunk6_3_checked, root7Node137Step3Chunk6_4_checked, root7Node137Step3Chunk6_5_checked, root7Node137Step3Chunk7_0_checked, root7Node137Step3Chunk7_1_checked, root7Node137Step3Chunk7_2_checked, root7Node137Step3Chunk7_3_checked, root7Node137Step3Chunk7_4_checked, root7Node137Step3Chunk7_5_checked, root7Node137Step3Chunk8_0_checked, root7Node137Step3Chunk8_1_checked, root7Node137Step3Chunk8_2_checked, root7Node137Step3Chunk8_3_checked, root7Node137Step3Chunk8_4_checked, root7Node137Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node137Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(0,0),(6,4)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(4,5),(5,5),(8,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(1,5),(3,5),(7,5)]
  | 33 => [(0,3),(6,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(4,4),(7,2)]
  | 36 => [(1,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,2)]
  | 42 => [(1,3),(3,3),(5,3),(7,3)]
  | 43 => [(4,1),(7,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(6,5)]
  | 50 => [(5,2),(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(7,0)]
  | 55 => [(2,3),(2,5),(4,5)]
  | 56 => [(8,4)]
  | 57 => [(1,4),(6,4)]
  | 58 => [(0,5),(1,2)]
  | 59 => [(4,4),(8,4)]
  | _ => [(0,0),(6,4)]
def root7Node137Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,5),(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(7,2)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(5,2),(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node137Domains4_fast_eq : root7Node137Domains4 = expandDomains root7Node137Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node137Domains4 v = expandDomains root7Node137Domains4Fast v from by decide) v
theorem root7Node137Step4Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root7Node137Domains3 root7Node137Domains4 = true := by
  exact checkNarrowing_of_fast _ root7Node137Domains3 root7Node137Domains4
    root7Node137Domains3Fast root7Node137Domains4Fast
    root7Node137Domains3_fast_eq root7Node137Domains4_fast_eq (by decide)
theorem root7Node137Step4_checked :
    checkReplacement table35 root7Node137Domains3 root7Node137Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node137Step4Chunk0_0_checked, root7Node137Step4Chunk0_1_checked, root7Node137Step4Chunk0_2_checked, root7Node137Step4Chunk0_3_checked, root7Node137Step4Chunk0_4_checked, root7Node137Step4Chunk0_5_checked, root7Node137Step4Chunk1_0_checked, root7Node137Step4Chunk1_1_checked, root7Node137Step4Chunk1_2_checked, root7Node137Step4Chunk1_3_checked, root7Node137Step4Chunk1_4_checked, root7Node137Step4Chunk1_5_checked, root7Node137Step4Chunk2_0_checked, root7Node137Step4Chunk2_1_checked, root7Node137Step4Chunk2_2_checked, root7Node137Step4Chunk2_3_checked, root7Node137Step4Chunk2_4_checked, root7Node137Step4Chunk2_5_checked, root7Node137Step4Chunk3_0_checked, root7Node137Step4Chunk3_1_checked, root7Node137Step4Chunk3_2_checked, root7Node137Step4Chunk3_3_checked, root7Node137Step4Chunk3_4_checked, root7Node137Step4Chunk3_5_checked, root7Node137Step4Chunk4_0_checked, root7Node137Step4Chunk4_1_checked, root7Node137Step4Chunk4_2_checked, root7Node137Step4Chunk4_3_checked, root7Node137Step4Chunk4_4_checked, root7Node137Step4Chunk4_5_checked, root7Node137Step4Chunk5_0_checked, root7Node137Step4Chunk5_1_checked, root7Node137Step4Chunk5_2_checked, root7Node137Step4Chunk5_3_checked, root7Node137Step4Chunk5_4_checked, root7Node137Step4Chunk5_5_checked, root7Node137Step4Chunk6_0_checked, root7Node137Step4Chunk6_1_checked, root7Node137Step4Chunk6_2_checked, root7Node137Step4Chunk6_3_checked, root7Node137Step4Chunk6_4_checked, root7Node137Step4Chunk6_5_checked, root7Node137Step4Chunk7_0_checked, root7Node137Step4Chunk7_1_checked, root7Node137Step4Chunk7_2_checked, root7Node137Step4Chunk7_3_checked, root7Node137Step4Chunk7_4_checked, root7Node137Step4Chunk7_5_checked, root7Node137Step4Chunk8_0_checked, root7Node137Step4Chunk8_1_checked, root7Node137Step4Chunk8_2_checked, root7Node137Step4Chunk8_3_checked, root7Node137Step4Chunk8_4_checked, root7Node137Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node138Domains0 : Domains 61 State := restrict root7Node137Domains4 16 (5,0)
def root7Node138Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,5),(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(7,2)]
  | 36 => some [(1,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(5,2),(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node138Domains0_fast_eq : root7Node138Domains0 = expandDomains root7Node138Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node138Domains0 v = expandDomains root7Node138Domains0Fast v from by decide) v
def root7Node138Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(0,0)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(4,5),(5,5),(8,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(5,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(4,4),(7,2)]
  | 36 => [(1,4)]
  | 37 => [(0,5)]
  | 38 => [(4,4)]
  | 39 => [(1,4)]
  | 40 => [(0,5)]
  | 41 => [(2,0)]
  | 42 => [(7,3)]
  | 43 => [(4,1),(7,5)]
  | 44 => [(6,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(6,0)]
  | 48 => [(3,1)]
  | 49 => [(0,1)]
  | 50 => [(5,2),(8,2)]
  | 51 => [(8,0)]
  | 52 => [(7,3)]
  | 53 => [(8,2)]
  | 54 => [(5,0)]
  | 55 => [(4,5)]
  | 56 => [(8,4)]
  | 57 => [(6,4)]
  | 58 => [(1,2)]
  | 59 => [(8,4)]
  | _ => [(0,0)]
def root7Node138Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5),(5,5),(8,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(5,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(4,4),(7,2)]
  | 36 => some [(1,4)]
  | 37 => some [(0,5)]
  | 38 => some [(4,4)]
  | 39 => some [(1,4)]
  | 40 => some [(0,5)]
  | 41 => some [(2,0)]
  | 42 => some [(7,3)]
  | 43 => some [(4,1),(7,5)]
  | 44 => some [(6,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(6,0)]
  | 48 => some [(3,1)]
  | 49 => some [(0,1)]
  | 50 => some [(5,2),(8,2)]
  | 51 => some [(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(8,2)]
  | 54 => some [(5,0)]
  | 55 => some [(4,5)]
  | 56 => some [(8,4)]
  | 57 => some [(6,4)]
  | 58 => some [(1,2)]
  | 59 => some [(8,4)]
  | _ => some [(0,0)]
theorem root7Node138Domains1_fast_eq : root7Node138Domains1 = expandDomains root7Node138Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node138Domains1 v = expandDomains root7Node138Domains1Fast v from by decide) v
theorem root7Node138Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node138Domains0 root7Node138Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node138Domains0 root7Node138Domains1
    root7Node138Domains0Fast root7Node138Domains1Fast
    root7Node138Domains0_fast_eq root7Node138Domains1_fast_eq (by decide)
theorem root7Node138Step1_checked :
    checkReplacement table39 root7Node138Domains0 root7Node138Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node138Step1Chunk0_0_checked, root7Node138Step1Chunk0_1_checked, root7Node138Step1Chunk0_2_checked, root7Node138Step1Chunk0_3_checked, root7Node138Step1Chunk0_4_checked, root7Node138Step1Chunk0_5_checked, root7Node138Step1Chunk1_0_checked, root7Node138Step1Chunk1_1_checked, root7Node138Step1Chunk1_2_checked, root7Node138Step1Chunk1_3_checked, root7Node138Step1Chunk1_4_checked, root7Node138Step1Chunk1_5_checked, root7Node138Step1Chunk2_0_checked, root7Node138Step1Chunk2_1_checked, root7Node138Step1Chunk2_2_checked, root7Node138Step1Chunk2_3_checked, root7Node138Step1Chunk2_4_checked, root7Node138Step1Chunk2_5_checked, root7Node138Step1Chunk3_0_checked, root7Node138Step1Chunk3_1_checked, root7Node138Step1Chunk3_2_checked, root7Node138Step1Chunk3_3_checked, root7Node138Step1Chunk3_4_checked, root7Node138Step1Chunk3_5_checked, root7Node138Step1Chunk4_0_checked, root7Node138Step1Chunk4_1_checked, root7Node138Step1Chunk4_2_checked, root7Node138Step1Chunk4_3_checked, root7Node138Step1Chunk4_4_checked, root7Node138Step1Chunk4_5_checked, root7Node138Step1Chunk5_0_checked, root7Node138Step1Chunk5_1_checked, root7Node138Step1Chunk5_2_checked, root7Node138Step1Chunk5_3_checked, root7Node138Step1Chunk5_4_checked, root7Node138Step1Chunk5_5_checked, root7Node138Step1Chunk6_0_checked, root7Node138Step1Chunk6_1_checked, root7Node138Step1Chunk6_2_checked, root7Node138Step1Chunk6_3_checked, root7Node138Step1Chunk6_4_checked, root7Node138Step1Chunk6_5_checked, root7Node138Step1Chunk7_0_checked, root7Node138Step1Chunk7_1_checked, root7Node138Step1Chunk7_2_checked, root7Node138Step1Chunk7_3_checked, root7Node138Step1Chunk7_4_checked, root7Node138Step1Chunk7_5_checked, root7Node138Step1Chunk8_0_checked, root7Node138Step1Chunk8_1_checked, root7Node138Step1Chunk8_2_checked, root7Node138Step1Chunk8_3_checked, root7Node138Step1Chunk8_4_checked, root7Node138Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
