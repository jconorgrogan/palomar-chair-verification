module

public import SpectreFinite.RadiusFourRoot8Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable14
public import SpectreFinite.RadiusFourTable19
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable40

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node1Domains0 : Domains 61 State := restrict root8Node0Domains5 22 (1,1)
def root8Node1Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(1,5),(6,0),(7,5)]
  | 1 => some [(0,3),(1,1),(6,1),(7,1)]
  | 2 => some [(4,1),(5,1),(7,5),(8,1)]
  | 3 => some [(0,1),(0,2),(1,5),(6,0),(6,5)]
  | 4 => some [(0,4),(1,1),(6,1),(6,2),(7,1)]
  | 5 => some [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(7,3),(8,5)]
  | 6 => some [(4,0),(4,2),(7,0),(8,0)]
  | 7 => some [(5,3),(7,3),(8,3)]
  | 8 => some [(5,2),(5,5),(8,2),(8,5)]
  | 9 => some [(1,0),(7,0),(8,0)]
  | 10 => some [(2,3),(4,3),(7,1),(7,3),(8,3)]
  | 11 => some [(0,0),(0,3),(0,4),(0,5),(6,1),(6,2),(6,3),(6,4)]
  | 12 => some [(1,2),(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 13 => some [(0,1),(1,4),(7,4)]
  | 14 => some [(0,5),(6,2),(6,3)]
  | 15 => some [(4,4),(7,2),(8,4)]
  | 16 => some [(1,4),(4,0),(6,4),(7,4)]
  | 17 => some [(0,5),(1,2),(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,0),(1,5),(3,5),(4,2),(6,0),(7,0),(7,5)]
  | 19 => some [(0,3),(1,1),(4,3),(5,3),(6,1),(7,1),(8,3)]
  | 20 => some [(4,1),(7,5),(8,5)]
  | 21 => some [(0,2),(1,0),(6,0)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(5,1),(7,5),(8,1)]
  | 24 => some [(0,1),(0,2),(0,3),(6,0),(6,5)]
  | 25 => some [(0,4),(1,1),(3,1),(5,1),(6,2),(7,1),(8,1)]
  | 26 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 28 => some [(1,3),(3,3),(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(4,2),(5,2),(5,5),(8,2)]
  | 33 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 35 => some [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(4,1),(7,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5),(7,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2),(8,2)]
  | 54 => some [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(5,4),(6,5),(7,4),(8,4)]
  | _ => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
theorem root8Node1Domains0_fast_eq : root8Node1Domains0 = expandDomains root8Node1Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node1Domains0 v = expandDomains root8Node1Domains0Fast v from by decide) v
def root8Node1Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5),(7,5)]
  | 1 => [(0,3),(6,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(1,5),(6,5)]
  | 4 => [(0,4),(6,1),(6,2)]
  | 5 => [(4,5),(7,3),(8,5)]
  | 6 => [(4,2),(7,0)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0),(7,0)]
  | 10 => [(4,3),(7,1),(8,3)]
  | 11 => [(0,0),(6,3),(6,4)]
  | 12 => [(1,2),(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(4,0),(7,4)]
  | 17 => [(1,3),(6,3),(7,3)]
  | 18 => [(0,2),(1,0),(1,5),(3,5),(4,2),(6,0),(7,0),(7,5)]
  | 19 => [(0,3),(1,1),(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1),(5,1),(8,1)]
  | 24 => [(0,1),(0,2),(6,5)]
  | 25 => [(0,4),(1,1),(3,1),(5,1),(6,2),(7,1),(8,1)]
  | 26 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 28 => [(1,3),(3,3),(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5)]
  | 33 => [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 34 => [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 35 => [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(7,4),(8,4)]
  | 42 => [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 43 => [(4,5),(5,5),(8,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(4,1),(7,1),(8,1)]
  | 49 => [(0,2),(1,5),(6,5),(7,5)]
  | 50 => [(4,4),(7,2),(8,2)]
  | 51 => [(1,4),(4,0),(7,4),(8,0)]
  | 52 => [(0,5),(1,3),(6,3),(7,3)]
  | 53 => [(2,2),(2,4),(4,2),(8,2)]
  | 54 => [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 56 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(5,4),(6,5),(7,4),(8,4)]
  | _ => [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
def root8Node1Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5),(7,5)]
  | 1 => some [(0,3),(6,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(1,5),(6,5)]
  | 4 => some [(0,4),(6,1),(6,2)]
  | 5 => some [(4,5),(7,3),(8,5)]
  | 6 => some [(4,2),(7,0)]
  | 7 => some [(5,3),(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0),(7,0)]
  | 10 => some [(4,3),(7,1),(8,3)]
  | 11 => some [(0,0),(6,3),(6,4)]
  | 12 => some [(1,2),(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0),(7,4)]
  | 17 => some [(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,0),(1,5),(3,5),(4,2),(6,0),(7,0),(7,5)]
  | 19 => some [(0,3),(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(5,1),(8,1)]
  | 24 => some [(0,1),(0,2),(6,5)]
  | 25 => some [(0,4),(1,1),(3,1),(5,1),(6,2),(7,1),(8,1)]
  | 26 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 28 => some [(1,3),(3,3),(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(1,0),(3,0),(5,0),(5,3),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 35 => some [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(7,4),(8,4)]
  | 42 => some [(0,0),(1,3),(1,4),(6,3),(6,4)]
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(4,1),(7,1),(8,1)]
  | 49 => some [(0,2),(1,5),(6,5),(7,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(0,5),(1,3),(6,3),(7,3)]
  | 53 => some [(2,2),(2,4),(4,2),(8,2)]
  | 54 => some [(1,3),(3,3),(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,1),(1,2),(6,2),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(5,4),(6,5),(7,4),(8,4)]
  | _ => some [(0,0),(0,4),(0,5),(6,2),(6,3),(6,4)]
theorem root8Node1Domains1_fast_eq : root8Node1Domains1 = expandDomains root8Node1Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node1Domains1 v = expandDomains root8Node1Domains1Fast v from by decide) v
theorem root8Node1Step1Chunk0_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk0_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk1_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk2_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk3_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk4_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk5_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk6_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk7_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_0⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_1⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_2⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_3⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_4⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1Chunk8_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_5⟩
      root8Node1Domains0 root8Node1Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains0 root8Node1Domains1
    root8Node1Domains0Fast root8Node1Domains1Fast
    root8Node1Domains0_fast_eq root8Node1Domains1_fast_eq (by decide)
theorem root8Node1Step1_checked :
    checkReplacement table14 root8Node1Domains0 root8Node1Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node1Step1Chunk0_0_checked, root8Node1Step1Chunk0_1_checked, root8Node1Step1Chunk0_2_checked, root8Node1Step1Chunk0_3_checked, root8Node1Step1Chunk0_4_checked, root8Node1Step1Chunk0_5_checked, root8Node1Step1Chunk1_0_checked, root8Node1Step1Chunk1_1_checked, root8Node1Step1Chunk1_2_checked, root8Node1Step1Chunk1_3_checked, root8Node1Step1Chunk1_4_checked, root8Node1Step1Chunk1_5_checked, root8Node1Step1Chunk2_0_checked, root8Node1Step1Chunk2_1_checked, root8Node1Step1Chunk2_2_checked, root8Node1Step1Chunk2_3_checked, root8Node1Step1Chunk2_4_checked, root8Node1Step1Chunk2_5_checked, root8Node1Step1Chunk3_0_checked, root8Node1Step1Chunk3_1_checked, root8Node1Step1Chunk3_2_checked, root8Node1Step1Chunk3_3_checked, root8Node1Step1Chunk3_4_checked, root8Node1Step1Chunk3_5_checked, root8Node1Step1Chunk4_0_checked, root8Node1Step1Chunk4_1_checked, root8Node1Step1Chunk4_2_checked, root8Node1Step1Chunk4_3_checked, root8Node1Step1Chunk4_4_checked, root8Node1Step1Chunk4_5_checked, root8Node1Step1Chunk5_0_checked, root8Node1Step1Chunk5_1_checked, root8Node1Step1Chunk5_2_checked, root8Node1Step1Chunk5_3_checked, root8Node1Step1Chunk5_4_checked, root8Node1Step1Chunk5_5_checked, root8Node1Step1Chunk6_0_checked, root8Node1Step1Chunk6_1_checked, root8Node1Step1Chunk6_2_checked, root8Node1Step1Chunk6_3_checked, root8Node1Step1Chunk6_4_checked, root8Node1Step1Chunk6_5_checked, root8Node1Step1Chunk7_0_checked, root8Node1Step1Chunk7_1_checked, root8Node1Step1Chunk7_2_checked, root8Node1Step1Chunk7_3_checked, root8Node1Step1Chunk7_4_checked, root8Node1Step1Chunk7_5_checked, root8Node1Step1Chunk8_0_checked, root8Node1Step1Chunk8_1_checked, root8Node1Step1Chunk8_2_checked, root8Node1Step1Chunk8_3_checked, root8Node1Step1Chunk8_4_checked, root8Node1Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node1Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5),(7,5)]
  | 1 => [(0,3),(6,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(1,5),(6,5)]
  | 4 => [(0,4),(6,1),(6,2)]
  | 5 => [(4,5),(7,3),(8,5)]
  | 6 => [(4,2),(7,0)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0),(7,0)]
  | 10 => [(4,3),(7,1),(8,3)]
  | 11 => [(0,0),(6,3),(6,4)]
  | 12 => [(1,2),(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(4,0),(7,4)]
  | 17 => [(1,3),(6,3),(7,3)]
  | 18 => [(0,2),(1,0),(1,5),(3,5),(4,2),(6,0),(7,0),(7,5)]
  | 19 => [(0,3),(1,1),(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1),(5,1),(8,1)]
  | 24 => [(0,1),(0,2),(6,5)]
  | 25 => [(0,4),(1,1),(6,2)]
  | 26 => [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 28 => [(1,3),(3,3),(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5)]
  | 33 => [(1,0),(3,0),(5,0),(7,0)]
  | 34 => [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 35 => [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(8,4)]
  | 42 => [(0,0),(1,4),(6,4)]
  | 43 => [(4,5),(5,5),(8,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(7,1),(8,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(4,4),(7,2),(8,2)]
  | 51 => [(1,4),(4,0),(7,4),(8,0)]
  | 52 => [(1,3),(7,3)]
  | 53 => [(4,2),(8,2)]
  | 54 => [(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(5,5),(7,3),(8,5)]
  | 56 => [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => [(0,4),(1,2),(6,2)]
  | 59 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | _ => [(0,0),(0,5),(6,3),(6,4)]
def root8Node1Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5),(7,5)]
  | 1 => some [(0,3),(6,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(1,5),(6,5)]
  | 4 => some [(0,4),(6,1),(6,2)]
  | 5 => some [(4,5),(7,3),(8,5)]
  | 6 => some [(4,2),(7,0)]
  | 7 => some [(5,3),(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0),(7,0)]
  | 10 => some [(4,3),(7,1),(8,3)]
  | 11 => some [(0,0),(6,3),(6,4)]
  | 12 => some [(1,2),(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0),(7,4)]
  | 17 => some [(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,0),(1,5),(3,5),(4,2),(6,0),(7,0),(7,5)]
  | 19 => some [(0,3),(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(5,1),(8,1)]
  | 24 => some [(0,1),(0,2),(6,5)]
  | 25 => some [(0,4),(1,1),(6,2)]
  | 26 => some [(0,5),(1,2),(3,2),(6,3),(7,2)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0),(7,4)]
  | 28 => some [(1,3),(3,3),(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(1,0),(3,0),(5,0),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 35 => some [(1,1),(3,1),(5,1),(7,1),(8,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,4)]
  | 43 => some [(4,5),(5,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(4,4),(7,2),(8,2)]
  | 51 => some [(1,4),(4,0),(7,4),(8,0)]
  | 52 => some [(1,3),(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,5),(7,3),(8,5)]
  | 56 => some [(4,1),(5,1),(5,4),(7,5),(8,1)]
  | 57 => some [(0,1),(0,2),(6,0),(6,4),(6,5)]
  | 58 => some [(0,4),(1,2),(6,2)]
  | 59 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | _ => some [(0,0),(0,5),(6,3),(6,4)]
theorem root8Node1Domains2_fast_eq : root8Node1Domains2 = expandDomains root8Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node1Domains2 v = expandDomains root8Node1Domains2Fast v from by decide) v
theorem root8Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root8Node1Domains1 root8Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains1 root8Node1Domains2
    root8Node1Domains1Fast root8Node1Domains2Fast
    root8Node1Domains1_fast_eq root8Node1Domains2_fast_eq (by decide)
theorem root8Node1Step2_checked :
    checkReplacement table40 root8Node1Domains1 root8Node1Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node1Step2Chunk0_0_checked, root8Node1Step2Chunk0_1_checked, root8Node1Step2Chunk0_2_checked, root8Node1Step2Chunk0_3_checked, root8Node1Step2Chunk0_4_checked, root8Node1Step2Chunk0_5_checked, root8Node1Step2Chunk1_0_checked, root8Node1Step2Chunk1_1_checked, root8Node1Step2Chunk1_2_checked, root8Node1Step2Chunk1_3_checked, root8Node1Step2Chunk1_4_checked, root8Node1Step2Chunk1_5_checked, root8Node1Step2Chunk2_0_checked, root8Node1Step2Chunk2_1_checked, root8Node1Step2Chunk2_2_checked, root8Node1Step2Chunk2_3_checked, root8Node1Step2Chunk2_4_checked, root8Node1Step2Chunk2_5_checked, root8Node1Step2Chunk3_0_checked, root8Node1Step2Chunk3_1_checked, root8Node1Step2Chunk3_2_checked, root8Node1Step2Chunk3_3_checked, root8Node1Step2Chunk3_4_checked, root8Node1Step2Chunk3_5_checked, root8Node1Step2Chunk4_0_checked, root8Node1Step2Chunk4_1_checked, root8Node1Step2Chunk4_2_checked, root8Node1Step2Chunk4_3_checked, root8Node1Step2Chunk4_4_checked, root8Node1Step2Chunk4_5_checked, root8Node1Step2Chunk5_0_checked, root8Node1Step2Chunk5_1_checked, root8Node1Step2Chunk5_2_checked, root8Node1Step2Chunk5_3_checked, root8Node1Step2Chunk5_4_checked, root8Node1Step2Chunk5_5_checked, root8Node1Step2Chunk6_0_checked, root8Node1Step2Chunk6_1_checked, root8Node1Step2Chunk6_2_checked, root8Node1Step2Chunk6_3_checked, root8Node1Step2Chunk6_4_checked, root8Node1Step2Chunk6_5_checked, root8Node1Step2Chunk7_0_checked, root8Node1Step2Chunk7_1_checked, root8Node1Step2Chunk7_2_checked, root8Node1Step2Chunk7_3_checked, root8Node1Step2Chunk7_4_checked, root8Node1Step2Chunk7_5_checked, root8Node1Step2Chunk8_0_checked, root8Node1Step2Chunk8_1_checked, root8Node1Step2Chunk8_2_checked, root8Node1Step2Chunk8_3_checked, root8Node1Step2Chunk8_4_checked, root8Node1Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node1Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5),(7,5)]
  | 1 => [(0,3),(6,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(1,5),(6,5)]
  | 4 => [(0,4),(6,1),(6,2)]
  | 5 => [(4,5),(7,3),(8,5)]
  | 6 => [(4,2),(7,0)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0),(7,0)]
  | 10 => [(4,3),(7,1),(8,3)]
  | 11 => [(0,0),(6,3),(6,4)]
  | 12 => [(1,2),(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(4,0),(7,4)]
  | 17 => [(1,3),(6,3),(7,3)]
  | 18 => [(0,2),(1,5),(3,5),(7,5)]
  | 19 => [(0,3),(1,1),(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1),(5,1),(8,1)]
  | 24 => [(0,1),(0,2),(6,5)]
  | 25 => [(0,4),(1,1),(6,2)]
  | 26 => [(0,5),(1,2),(3,2),(6,3)]
  | 27 => [(2,0),(2,2),(2,4),(4,0)]
  | 28 => [(1,3),(3,3),(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5)]
  | 33 => [(1,0),(3,0),(5,0),(7,0)]
  | 34 => [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 35 => [(1,1),(3,1),(5,1),(7,1)]
  | 36 => [(0,1),(6,5)]
  | 37 => [(0,4),(6,2)]
  | 38 => [(5,4),(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(8,4)]
  | 42 => [(0,0),(1,4),(6,4)]
  | 43 => [(4,5),(8,5)]
  | 44 => [(1,0),(7,0)]
  | 45 => [(4,3),(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(7,1),(8,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(7,4),(8,0)]
  | 52 => [(1,3),(7,3)]
  | 53 => [(4,2),(8,2)]
  | 54 => [(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(5,5),(7,3),(8,5)]
  | 56 => [(5,1),(5,4),(8,1)]
  | 57 => [(0,1),(6,4),(6,5)]
  | 58 => [(0,4),(1,2),(6,2)]
  | 59 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | _ => [(0,0),(0,5),(6,3),(6,4)]
def root8Node1Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5),(7,5)]
  | 1 => some [(0,3),(6,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(1,5),(6,5)]
  | 4 => some [(0,4),(6,1),(6,2)]
  | 5 => some [(4,5),(7,3),(8,5)]
  | 6 => some [(4,2),(7,0)]
  | 7 => some [(5,3),(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0),(7,0)]
  | 10 => some [(4,3),(7,1),(8,3)]
  | 11 => some [(0,0),(6,3),(6,4)]
  | 12 => some [(1,2),(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0),(7,4)]
  | 17 => some [(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,5),(3,5),(7,5)]
  | 19 => some [(0,3),(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(5,1),(8,1)]
  | 24 => some [(0,1),(0,2),(6,5)]
  | 25 => some [(0,4),(1,1),(6,2)]
  | 26 => some [(0,5),(1,2),(3,2),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0)]
  | 28 => some [(1,3),(3,3),(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(1,0),(3,0),(5,0),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 35 => some [(1,1),(3,1),(5,1),(7,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,4)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(7,4),(8,0)]
  | 52 => some [(1,3),(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,5),(7,3),(8,5)]
  | 56 => some [(5,1),(5,4),(8,1)]
  | 57 => some [(0,1),(6,4),(6,5)]
  | 58 => some [(0,4),(1,2),(6,2)]
  | 59 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | _ => some [(0,0),(0,5),(6,3),(6,4)]
theorem root8Node1Domains3_fast_eq : root8Node1Domains3 = expandDomains root8Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node1Domains3 v = expandDomains root8Node1Domains3Fast v from by decide) v
theorem root8Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root8Node1Domains2 root8Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node1Domains2 root8Node1Domains3
    root8Node1Domains2Fast root8Node1Domains3Fast
    root8Node1Domains2_fast_eq root8Node1Domains3_fast_eq (by decide)
theorem root8Node1Step3_checked :
    checkReplacement table36 root8Node1Domains2 root8Node1Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node1Step3Chunk0_0_checked, root8Node1Step3Chunk0_1_checked, root8Node1Step3Chunk0_2_checked, root8Node1Step3Chunk0_3_checked, root8Node1Step3Chunk0_4_checked, root8Node1Step3Chunk0_5_checked, root8Node1Step3Chunk1_0_checked, root8Node1Step3Chunk1_1_checked, root8Node1Step3Chunk1_2_checked, root8Node1Step3Chunk1_3_checked, root8Node1Step3Chunk1_4_checked, root8Node1Step3Chunk1_5_checked, root8Node1Step3Chunk2_0_checked, root8Node1Step3Chunk2_1_checked, root8Node1Step3Chunk2_2_checked, root8Node1Step3Chunk2_3_checked, root8Node1Step3Chunk2_4_checked, root8Node1Step3Chunk2_5_checked, root8Node1Step3Chunk3_0_checked, root8Node1Step3Chunk3_1_checked, root8Node1Step3Chunk3_2_checked, root8Node1Step3Chunk3_3_checked, root8Node1Step3Chunk3_4_checked, root8Node1Step3Chunk3_5_checked, root8Node1Step3Chunk4_0_checked, root8Node1Step3Chunk4_1_checked, root8Node1Step3Chunk4_2_checked, root8Node1Step3Chunk4_3_checked, root8Node1Step3Chunk4_4_checked, root8Node1Step3Chunk4_5_checked, root8Node1Step3Chunk5_0_checked, root8Node1Step3Chunk5_1_checked, root8Node1Step3Chunk5_2_checked, root8Node1Step3Chunk5_3_checked, root8Node1Step3Chunk5_4_checked, root8Node1Step3Chunk5_5_checked, root8Node1Step3Chunk6_0_checked, root8Node1Step3Chunk6_1_checked, root8Node1Step3Chunk6_2_checked, root8Node1Step3Chunk6_3_checked, root8Node1Step3Chunk6_4_checked, root8Node1Step3Chunk6_5_checked, root8Node1Step3Chunk7_0_checked, root8Node1Step3Chunk7_1_checked, root8Node1Step3Chunk7_2_checked, root8Node1Step3Chunk7_3_checked, root8Node1Step3Chunk7_4_checked, root8Node1Step3Chunk7_5_checked, root8Node1Step3Chunk8_0_checked, root8Node1Step3Chunk8_1_checked, root8Node1Step3Chunk8_2_checked, root8Node1Step3Chunk8_3_checked, root8Node1Step3Chunk8_4_checked, root8Node1Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node2Domains0 : Domains 61 State := restrict root8Node1Domains3 0 (1,5)
def root8Node2Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(0,3),(6,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(1,5),(6,5)]
  | 4 => some [(0,4),(6,1),(6,2)]
  | 5 => some [(4,5),(7,3),(8,5)]
  | 6 => some [(4,2),(7,0)]
  | 7 => some [(5,3),(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0),(7,0)]
  | 10 => some [(4,3),(7,1),(8,3)]
  | 11 => some [(0,0),(6,3),(6,4)]
  | 12 => some [(1,2),(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0),(7,4)]
  | 17 => some [(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,5),(3,5),(7,5)]
  | 19 => some [(0,3),(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(5,1),(8,1)]
  | 24 => some [(0,1),(0,2),(6,5)]
  | 25 => some [(0,4),(1,1),(6,2)]
  | 26 => some [(0,5),(1,2),(3,2),(6,3)]
  | 27 => some [(2,0),(2,2),(2,4),(4,0)]
  | 28 => some [(1,3),(3,3),(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(1,0),(3,0),(5,0),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 35 => some [(1,1),(3,1),(5,1),(7,1)]
  | 36 => some [(0,1),(6,5)]
  | 37 => some [(0,4),(6,2)]
  | 38 => some [(5,4),(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,4)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(1,0),(7,0)]
  | 45 => some [(4,3),(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(7,4),(8,0)]
  | 52 => some [(1,3),(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,5),(7,3),(8,5)]
  | 56 => some [(5,1),(5,4),(8,1)]
  | 57 => some [(0,1),(6,4),(6,5)]
  | 58 => some [(0,4),(1,2),(6,2)]
  | 59 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | _ => some [(0,0),(0,5),(6,3),(6,4)]
theorem root8Node2Domains0_fast_eq : root8Node2Domains0 = expandDomains root8Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node2Domains0 v = expandDomains root8Node2Domains0Fast v from by decide) v
def root8Node2Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(1,5),(6,5)]
  | 4 => [(0,4),(6,1),(6,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0),(7,0)]
  | 10 => [(4,3),(7,1),(8,3)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(4,0),(7,4)]
  | 17 => [(1,3),(6,3),(7,3)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1),(5,1),(8,1)]
  | 24 => [(0,1),(0,2),(6,5)]
  | 25 => [(0,4),(1,1),(6,2)]
  | 26 => [(0,5),(1,2),(3,2)]
  | 27 => [(2,0),(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5)]
  | 33 => [(1,0),(3,0),(5,0),(7,0)]
  | 34 => [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 35 => [(3,1),(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(8,4)]
  | 42 => [(0,0),(1,4),(6,4)]
  | 43 => [(4,5),(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(7,1),(8,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(7,4),(8,0)]
  | 52 => [(1,3),(7,3)]
  | 53 => [(4,2),(8,2)]
  | 54 => [(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(5,5),(7,3),(8,5)]
  | 56 => [(5,1),(5,4),(8,1)]
  | 57 => [(0,1),(6,4),(6,5)]
  | 58 => [(0,4),(1,2),(6,2)]
  | 59 => [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | _ => [(0,0),(0,5),(6,3),(6,4)]
def root8Node2Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(1,5),(6,5)]
  | 4 => some [(0,4),(6,1),(6,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0),(7,0)]
  | 10 => some [(4,3),(7,1),(8,3)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0),(7,4)]
  | 17 => some [(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(5,1),(8,1)]
  | 24 => some [(0,1),(0,2),(6,5)]
  | 25 => some [(0,4),(1,1),(6,2)]
  | 26 => some [(0,5),(1,2),(3,2)]
  | 27 => some [(2,0),(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(1,0),(3,0),(5,0),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 35 => some [(3,1),(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(1,4),(6,4)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(7,4),(8,0)]
  | 52 => some [(1,3),(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(5,5),(7,3),(8,5)]
  | 56 => some [(5,1),(5,4),(8,1)]
  | 57 => some [(0,1),(6,4),(6,5)]
  | 58 => some [(0,4),(1,2),(6,2)]
  | 59 => some [(1,4),(3,4),(5,4),(7,4),(8,4)]
  | _ => some [(0,0),(0,5),(6,3),(6,4)]
theorem root8Node2Domains1_fast_eq : root8Node2Domains1 = expandDomains root8Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node2Domains1 v = expandDomains root8Node2Domains1Fast v from by decide) v
theorem root8Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root8Node2Domains0 root8Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains0 root8Node2Domains1
    root8Node2Domains0Fast root8Node2Domains1Fast
    root8Node2Domains0_fast_eq root8Node2Domains1_fast_eq (by decide)
theorem root8Node2Step1_checked :
    checkReplacement table19 root8Node2Domains0 root8Node2Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node2Step1Chunk0_0_checked, root8Node2Step1Chunk0_1_checked, root8Node2Step1Chunk0_2_checked, root8Node2Step1Chunk0_3_checked, root8Node2Step1Chunk0_4_checked, root8Node2Step1Chunk0_5_checked, root8Node2Step1Chunk1_0_checked, root8Node2Step1Chunk1_1_checked, root8Node2Step1Chunk1_2_checked, root8Node2Step1Chunk1_3_checked, root8Node2Step1Chunk1_4_checked, root8Node2Step1Chunk1_5_checked, root8Node2Step1Chunk2_0_checked, root8Node2Step1Chunk2_1_checked, root8Node2Step1Chunk2_2_checked, root8Node2Step1Chunk2_3_checked, root8Node2Step1Chunk2_4_checked, root8Node2Step1Chunk2_5_checked, root8Node2Step1Chunk3_0_checked, root8Node2Step1Chunk3_1_checked, root8Node2Step1Chunk3_2_checked, root8Node2Step1Chunk3_3_checked, root8Node2Step1Chunk3_4_checked, root8Node2Step1Chunk3_5_checked, root8Node2Step1Chunk4_0_checked, root8Node2Step1Chunk4_1_checked, root8Node2Step1Chunk4_2_checked, root8Node2Step1Chunk4_3_checked, root8Node2Step1Chunk4_4_checked, root8Node2Step1Chunk4_5_checked, root8Node2Step1Chunk5_0_checked, root8Node2Step1Chunk5_1_checked, root8Node2Step1Chunk5_2_checked, root8Node2Step1Chunk5_3_checked, root8Node2Step1Chunk5_4_checked, root8Node2Step1Chunk5_5_checked, root8Node2Step1Chunk6_0_checked, root8Node2Step1Chunk6_1_checked, root8Node2Step1Chunk6_2_checked, root8Node2Step1Chunk6_3_checked, root8Node2Step1Chunk6_4_checked, root8Node2Step1Chunk6_5_checked, root8Node2Step1Chunk7_0_checked, root8Node2Step1Chunk7_1_checked, root8Node2Step1Chunk7_2_checked, root8Node2Step1Chunk7_3_checked, root8Node2Step1Chunk7_4_checked, root8Node2Step1Chunk7_5_checked, root8Node2Step1Chunk8_0_checked, root8Node2Step1Chunk8_1_checked, root8Node2Step1Chunk8_2_checked, root8Node2Step1Chunk8_3_checked, root8Node2Step1Chunk8_4_checked, root8Node2Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node2Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(1,5),(6,5)]
  | 4 => [(0,4),(6,1),(6,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0),(7,0)]
  | 10 => [(4,3),(7,1),(8,3)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(6,3)]
  | 15 => [(7,2)]
  | 16 => [(4,0),(7,4)]
  | 17 => [(1,3),(6,3),(7,3)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
  | 20 => [(4,1)]
  | 21 => [(0,2)]
  | 22 => [(1,1)]
  | 23 => [(4,1),(5,1),(8,1)]
  | 24 => [(0,1),(0,2),(6,5)]
  | 25 => [(0,4),(1,1),(6,2)]
  | 26 => [(0,5),(1,2),(3,2)]
  | 27 => [(2,0),(4,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5)]
  | 33 => [(1,0),(3,0),(5,0),(7,0)]
  | 34 => [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 35 => [(3,1),(5,1)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(1,4),(6,4)]
  | 40 => [(0,5),(1,2)]
  | 41 => [(4,4),(8,4)]
  | 42 => [(0,0),(6,4)]
  | 43 => [(4,5),(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
  | 46 => [(7,5)]
  | 47 => [(0,3),(6,0)]
  | 48 => [(7,1),(8,1)]
  | 49 => [(1,5),(7,5)]
  | 50 => [(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3)]
  | 53 => [(4,2),(8,2)]
  | 54 => [(5,0),(5,3),(8,0)]
  | 55 => [(4,5),(7,3),(8,5)]
  | 56 => [(5,1),(5,4),(8,1)]
  | 57 => [(0,1),(6,4)]
  | 58 => [(1,2),(6,2)]
  | 59 => [(7,4),(8,4)]
  | _ => [(0,0),(6,3),(6,4)]
def root8Node2Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(1,5),(6,5)]
  | 4 => some [(0,4),(6,1),(6,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0),(7,0)]
  | 10 => some [(4,3),(7,1),(8,3)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(6,3)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0),(7,4)]
  | 17 => some [(1,3),(6,3),(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
  | 20 => some [(4,1)]
  | 21 => some [(0,2)]
  | 22 => some [(1,1)]
  | 23 => some [(4,1),(5,1),(8,1)]
  | 24 => some [(0,1),(0,2),(6,5)]
  | 25 => some [(0,4),(1,1),(6,2)]
  | 26 => some [(0,5),(1,2),(3,2)]
  | 27 => some [(2,0),(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5)]
  | 33 => some [(1,0),(3,0),(5,0),(7,0)]
  | 34 => some [(2,1),(2,3),(2,5),(4,3),(4,5)]
  | 35 => some [(3,1),(5,1)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(1,4),(6,4)]
  | 40 => some [(0,5),(1,2)]
  | 41 => some [(4,4),(8,4)]
  | 42 => some [(0,0),(6,4)]
  | 43 => some [(4,5),(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3),(6,0)]
  | 48 => some [(7,1),(8,1)]
  | 49 => some [(1,5),(7,5)]
  | 50 => some [(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3)]
  | 53 => some [(4,2),(8,2)]
  | 54 => some [(5,0),(5,3),(8,0)]
  | 55 => some [(4,5),(7,3),(8,5)]
  | 56 => some [(5,1),(5,4),(8,1)]
  | 57 => some [(0,1),(6,4)]
  | 58 => some [(1,2),(6,2)]
  | 59 => some [(7,4),(8,4)]
  | _ => some [(0,0),(6,3),(6,4)]
theorem root8Node2Domains2_fast_eq : root8Node2Domains2 = expandDomains root8Node2Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node2Domains2 v = expandDomains root8Node2Domains2Fast v from by decide) v
theorem root8Node2Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root8Node2Domains1 root8Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node2Domains1 root8Node2Domains2
    root8Node2Domains1Fast root8Node2Domains2Fast
    root8Node2Domains1_fast_eq root8Node2Domains2_fast_eq (by decide)
theorem root8Node2Step2_checked :
    checkReplacement table39 root8Node2Domains1 root8Node2Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node2Step2Chunk0_0_checked, root8Node2Step2Chunk0_1_checked, root8Node2Step2Chunk0_2_checked, root8Node2Step2Chunk0_3_checked, root8Node2Step2Chunk0_4_checked, root8Node2Step2Chunk0_5_checked, root8Node2Step2Chunk1_0_checked, root8Node2Step2Chunk1_1_checked, root8Node2Step2Chunk1_2_checked, root8Node2Step2Chunk1_3_checked, root8Node2Step2Chunk1_4_checked, root8Node2Step2Chunk1_5_checked, root8Node2Step2Chunk2_0_checked, root8Node2Step2Chunk2_1_checked, root8Node2Step2Chunk2_2_checked, root8Node2Step2Chunk2_3_checked, root8Node2Step2Chunk2_4_checked, root8Node2Step2Chunk2_5_checked, root8Node2Step2Chunk3_0_checked, root8Node2Step2Chunk3_1_checked, root8Node2Step2Chunk3_2_checked, root8Node2Step2Chunk3_3_checked, root8Node2Step2Chunk3_4_checked, root8Node2Step2Chunk3_5_checked, root8Node2Step2Chunk4_0_checked, root8Node2Step2Chunk4_1_checked, root8Node2Step2Chunk4_2_checked, root8Node2Step2Chunk4_3_checked, root8Node2Step2Chunk4_4_checked, root8Node2Step2Chunk4_5_checked, root8Node2Step2Chunk5_0_checked, root8Node2Step2Chunk5_1_checked, root8Node2Step2Chunk5_2_checked, root8Node2Step2Chunk5_3_checked, root8Node2Step2Chunk5_4_checked, root8Node2Step2Chunk5_5_checked, root8Node2Step2Chunk6_0_checked, root8Node2Step2Chunk6_1_checked, root8Node2Step2Chunk6_2_checked, root8Node2Step2Chunk6_3_checked, root8Node2Step2Chunk6_4_checked, root8Node2Step2Chunk6_5_checked, root8Node2Step2Chunk7_0_checked, root8Node2Step2Chunk7_1_checked, root8Node2Step2Chunk7_2_checked, root8Node2Step2Chunk7_3_checked, root8Node2Step2Chunk7_4_checked, root8Node2Step2Chunk7_5_checked, root8Node2Step2Chunk8_0_checked, root8Node2Step2Chunk8_1_checked, root8Node2Step2Chunk8_2_checked, root8Node2Step2Chunk8_3_checked, root8Node2Step2Chunk8_4_checked, root8Node2Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
