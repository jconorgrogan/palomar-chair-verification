module

public import SpectreFinite.RadiusFourRoot5Part6
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable10
public import SpectreFinite.RadiusFourTable22
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable3
public import SpectreFinite.RadiusFourTable5

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node19Domains0 : Domains 61 State := restrict root5Node15Domains1 0 (6,5)
def root5Node19Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(6,4),(6,5)]
  | 4 => some [(0,4),(1,2),(6,2),(7,2)]
  | 5 => some [(5,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,5),(7,5)]
  | 9 => some [(0,3),(1,0),(3,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1)]
  | 11 => some [(0,5),(6,3)]
  | 12 => some [(4,4),(7,2)]
  | 13 => some [(1,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(0,2),(6,0)]
  | 19 => some [(1,1),(7,1)]
  | 20 => some [(4,1),(7,5)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(3,1),(7,1)]
  | 23 => some [(0,1),(1,5),(6,5)]
  | 24 => some [(0,4),(6,1),(6,2)]
  | 25 => some [(5,1),(5,4),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
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
theorem root5Node19Domains0_fast_eq : root5Node19Domains0 = expandDomains root5Node19Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node19Domains0 v = expandDomains root5Node19Domains0Fast v from by decide) v
def root5Node19Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0),(6,4)]
  | 4 => [(1,2),(7,2)]
  | 5 => [(5,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(1,5),(3,5),(7,5)]
  | 9 => [(0,3),(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,5),(6,3)]
  | 12 => [(4,4),(7,2)]
  | 13 => [(1,4),(7,4)]
  | 14 => [(0,5),(6,3)]
  | 15 => [(2,0),(2,2),(2,4)]
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(5,2)]
  | 18 => [(0,2),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(0,2),(6,0)]
  | 22 => [(1,1),(3,1),(7,1)]
  | 23 => [(0,1),(6,5)]
  | 24 => [(0,4),(6,2)]
  | 25 => [(5,1),(5,4),(8,4)]
  | 26 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0),(7,0)]
  | 33 => [(4,3),(7,1),(8,3)]
  | 34 => [(7,5),(8,5)]
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
def root5Node19Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0),(6,4)]
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
  | 25 => some [(5,1),(5,4),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
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
theorem root5Node19Domains1_fast_eq : root5Node19Domains1 = expandDomains root5Node19Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node19Domains1 v = expandDomains root5Node19Domains1Fast v from by decide) v
theorem root5Node19Step1Chunk0_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_0⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk0_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_1⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk0_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_2⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk0_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_3⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk0_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_4⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk0_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows0_5⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk1_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_0⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk1_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_1⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk1_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_2⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk1_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_3⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk1_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_4⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk1_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows1_5⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk2_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_0⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk2_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_1⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk2_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_2⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk2_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_3⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk2_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_4⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk2_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows2_5⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk3_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_0⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk3_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_1⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk3_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_2⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk3_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_3⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk3_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_4⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk3_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows3_5⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk4_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_0⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk4_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_1⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk4_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_2⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk4_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_3⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk4_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_4⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk4_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows4_5⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk5_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_0⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk5_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_1⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk5_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_2⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk5_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_3⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk5_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_4⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk5_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows5_5⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk6_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_0⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk6_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_1⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk6_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_2⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk6_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_3⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk6_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_4⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk6_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows6_5⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk7_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_0⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk7_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_1⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk7_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_2⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk7_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_3⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk7_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_4⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk7_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows7_5⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk8_0_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_0⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk8_1_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_1⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk8_2_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_2⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk8_3_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_3⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk8_4_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_4⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1Chunk8_5_checked :
    checkNarrowing ⟨table3Scope, table3Rows8_5⟩
      root5Node19Domains0 root5Node19Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains0 root5Node19Domains1
    root5Node19Domains0Fast root5Node19Domains1Fast
    root5Node19Domains0_fast_eq root5Node19Domains1_fast_eq (by decide)
theorem root5Node19Step1_checked :
    checkReplacement table3 root5Node19Domains0 root5Node19Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node19Step1Chunk0_0_checked, root5Node19Step1Chunk0_1_checked, root5Node19Step1Chunk0_2_checked, root5Node19Step1Chunk0_3_checked, root5Node19Step1Chunk0_4_checked, root5Node19Step1Chunk0_5_checked, root5Node19Step1Chunk1_0_checked, root5Node19Step1Chunk1_1_checked, root5Node19Step1Chunk1_2_checked, root5Node19Step1Chunk1_3_checked, root5Node19Step1Chunk1_4_checked, root5Node19Step1Chunk1_5_checked, root5Node19Step1Chunk2_0_checked, root5Node19Step1Chunk2_1_checked, root5Node19Step1Chunk2_2_checked, root5Node19Step1Chunk2_3_checked, root5Node19Step1Chunk2_4_checked, root5Node19Step1Chunk2_5_checked, root5Node19Step1Chunk3_0_checked, root5Node19Step1Chunk3_1_checked, root5Node19Step1Chunk3_2_checked, root5Node19Step1Chunk3_3_checked, root5Node19Step1Chunk3_4_checked, root5Node19Step1Chunk3_5_checked, root5Node19Step1Chunk4_0_checked, root5Node19Step1Chunk4_1_checked, root5Node19Step1Chunk4_2_checked, root5Node19Step1Chunk4_3_checked, root5Node19Step1Chunk4_4_checked, root5Node19Step1Chunk4_5_checked, root5Node19Step1Chunk5_0_checked, root5Node19Step1Chunk5_1_checked, root5Node19Step1Chunk5_2_checked, root5Node19Step1Chunk5_3_checked, root5Node19Step1Chunk5_4_checked, root5Node19Step1Chunk5_5_checked, root5Node19Step1Chunk6_0_checked, root5Node19Step1Chunk6_1_checked, root5Node19Step1Chunk6_2_checked, root5Node19Step1Chunk6_3_checked, root5Node19Step1Chunk6_4_checked, root5Node19Step1Chunk6_5_checked, root5Node19Step1Chunk7_0_checked, root5Node19Step1Chunk7_1_checked, root5Node19Step1Chunk7_2_checked, root5Node19Step1Chunk7_3_checked, root5Node19Step1Chunk7_4_checked, root5Node19Step1Chunk7_5_checked, root5Node19Step1Chunk8_0_checked, root5Node19Step1Chunk8_1_checked, root5Node19Step1Chunk8_2_checked, root5Node19Step1Chunk8_3_checked, root5Node19Step1Chunk8_4_checked, root5Node19Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node19Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0),(6,4)]
  | 4 => [(1,2),(7,2)]
  | 5 => [(5,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(1,5),(3,5),(7,5)]
  | 9 => [(0,3),(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,5),(6,3)]
  | 12 => [(4,4),(7,2)]
  | 13 => [(1,4),(7,4)]
  | 14 => [(0,5),(6,3)]
  | 15 => [(2,0),(2,2),(2,4)]
  | 16 => [(1,3),(3,3),(7,3)]
  | 17 => [(5,2)]
  | 18 => [(0,2),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(0,2),(6,0)]
  | 22 => [(1,1),(3,1),(7,1)]
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
def root5Node19Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0),(6,4)]
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
theorem root5Node19Domains2_fast_eq : root5Node19Domains2 = expandDomains root5Node19Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node19Domains2 v = expandDomains root5Node19Domains2Fast v from by decide) v
theorem root5Node19Step2Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root5Node19Domains1 root5Node19Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node19Domains1 root5Node19Domains2
    root5Node19Domains1Fast root5Node19Domains2Fast
    root5Node19Domains1_fast_eq root5Node19Domains2_fast_eq (by decide)
theorem root5Node19Step2_checked :
    checkReplacement table10 root5Node19Domains1 root5Node19Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node19Step2Chunk0_0_checked, root5Node19Step2Chunk0_1_checked, root5Node19Step2Chunk0_2_checked, root5Node19Step2Chunk0_3_checked, root5Node19Step2Chunk0_4_checked, root5Node19Step2Chunk0_5_checked, root5Node19Step2Chunk1_0_checked, root5Node19Step2Chunk1_1_checked, root5Node19Step2Chunk1_2_checked, root5Node19Step2Chunk1_3_checked, root5Node19Step2Chunk1_4_checked, root5Node19Step2Chunk1_5_checked, root5Node19Step2Chunk2_0_checked, root5Node19Step2Chunk2_1_checked, root5Node19Step2Chunk2_2_checked, root5Node19Step2Chunk2_3_checked, root5Node19Step2Chunk2_4_checked, root5Node19Step2Chunk2_5_checked, root5Node19Step2Chunk3_0_checked, root5Node19Step2Chunk3_1_checked, root5Node19Step2Chunk3_2_checked, root5Node19Step2Chunk3_3_checked, root5Node19Step2Chunk3_4_checked, root5Node19Step2Chunk3_5_checked, root5Node19Step2Chunk4_0_checked, root5Node19Step2Chunk4_1_checked, root5Node19Step2Chunk4_2_checked, root5Node19Step2Chunk4_3_checked, root5Node19Step2Chunk4_4_checked, root5Node19Step2Chunk4_5_checked, root5Node19Step2Chunk5_0_checked, root5Node19Step2Chunk5_1_checked, root5Node19Step2Chunk5_2_checked, root5Node19Step2Chunk5_3_checked, root5Node19Step2Chunk5_4_checked, root5Node19Step2Chunk5_5_checked, root5Node19Step2Chunk6_0_checked, root5Node19Step2Chunk6_1_checked, root5Node19Step2Chunk6_2_checked, root5Node19Step2Chunk6_3_checked, root5Node19Step2Chunk6_4_checked, root5Node19Step2Chunk6_5_checked, root5Node19Step2Chunk7_0_checked, root5Node19Step2Chunk7_1_checked, root5Node19Step2Chunk7_2_checked, root5Node19Step2Chunk7_3_checked, root5Node19Step2Chunk7_4_checked, root5Node19Step2Chunk7_5_checked, root5Node19Step2Chunk8_0_checked, root5Node19Step2Chunk8_1_checked, root5Node19Step2Chunk8_2_checked, root5Node19Step2Chunk8_3_checked, root5Node19Step2Chunk8_4_checked, root5Node19Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node20Domains0 : Domains 61 State := restrict root5Node19Domains2 3 (0,0)
def root5Node20Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
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
theorem root5Node20Domains0_fast_eq : root5Node20Domains0 = expandDomains root5Node20Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node20Domains0 v = expandDomains root5Node20Domains0Fast v from by decide) v
def root5Node20Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(6,5)]
  | 1 => [(0,4)]
  | 2 => [(5,4)]
  | 3 => [(0,0)]
  | 4 => [(7,2)]
  | 5 => [(5,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3)]
  | 8 => [(1,5)]
  | 9 => [(6,1)]
  | 10 => [(4,1)]
  | 11 => [(0,5),(6,3)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(2,0)]
  | 16 => [(7,3)]
  | 17 => [(5,2)]
  | 18 => [(0,2),(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(3,1)]
  | 23 => [(0,1)]
  | 24 => [(6,2)]
  | 25 => [(8,4)]
  | 26 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(5,1),(5,4),(8,4)]
  | 36 => [(0,1),(6,4)]
  | 37 => [(1,2),(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(1,3),(7,3)]
  | 43 => [(7,5),(8,5)]
  | 44 => [(0,3),(1,0)]
  | 45 => [(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
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
def root5Node20Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,5)]
  | 1 => some [(0,4)]
  | 2 => some [(5,4)]
  | 3 => some [(0,0)]
  | 4 => some [(7,2)]
  | 5 => some [(5,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3)]
  | 8 => some [(1,5)]
  | 9 => some [(6,1)]
  | 10 => some [(4,1)]
  | 11 => some [(0,5),(6,3)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(2,0)]
  | 16 => some [(7,3)]
  | 17 => some [(5,2)]
  | 18 => some [(0,2),(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(3,1)]
  | 23 => some [(0,1)]
  | 24 => some [(6,2)]
  | 25 => some [(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
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
  | 42 => some [(1,3),(7,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
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
theorem root5Node20Domains1_fast_eq : root5Node20Domains1 = expandDomains root5Node20Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node20Domains1 v = expandDomains root5Node20Domains1Fast v from by decide) v
theorem root5Node20Step1Chunk0_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk0_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk0_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk0_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk0_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk0_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows0_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk1_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows1_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk2_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows2_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk3_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows3_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk4_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows4_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk5_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows5_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk6_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows6_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk7_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows7_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_0_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_0⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_1_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_1⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_2_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_2⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_3_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_3⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_4_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_4⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1Chunk8_5_checked :
    checkNarrowing ⟨table22Scope, table22Rows8_5⟩
      root5Node20Domains0 root5Node20Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains0 root5Node20Domains1
    root5Node20Domains0Fast root5Node20Domains1Fast
    root5Node20Domains0_fast_eq root5Node20Domains1_fast_eq (by decide)
theorem root5Node20Step1_checked :
    checkReplacement table22 root5Node20Domains0 root5Node20Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node20Step1Chunk0_0_checked, root5Node20Step1Chunk0_1_checked, root5Node20Step1Chunk0_2_checked, root5Node20Step1Chunk0_3_checked, root5Node20Step1Chunk0_4_checked, root5Node20Step1Chunk0_5_checked, root5Node20Step1Chunk1_0_checked, root5Node20Step1Chunk1_1_checked, root5Node20Step1Chunk1_2_checked, root5Node20Step1Chunk1_3_checked, root5Node20Step1Chunk1_4_checked, root5Node20Step1Chunk1_5_checked, root5Node20Step1Chunk2_0_checked, root5Node20Step1Chunk2_1_checked, root5Node20Step1Chunk2_2_checked, root5Node20Step1Chunk2_3_checked, root5Node20Step1Chunk2_4_checked, root5Node20Step1Chunk2_5_checked, root5Node20Step1Chunk3_0_checked, root5Node20Step1Chunk3_1_checked, root5Node20Step1Chunk3_2_checked, root5Node20Step1Chunk3_3_checked, root5Node20Step1Chunk3_4_checked, root5Node20Step1Chunk3_5_checked, root5Node20Step1Chunk4_0_checked, root5Node20Step1Chunk4_1_checked, root5Node20Step1Chunk4_2_checked, root5Node20Step1Chunk4_3_checked, root5Node20Step1Chunk4_4_checked, root5Node20Step1Chunk4_5_checked, root5Node20Step1Chunk5_0_checked, root5Node20Step1Chunk5_1_checked, root5Node20Step1Chunk5_2_checked, root5Node20Step1Chunk5_3_checked, root5Node20Step1Chunk5_4_checked, root5Node20Step1Chunk5_5_checked, root5Node20Step1Chunk6_0_checked, root5Node20Step1Chunk6_1_checked, root5Node20Step1Chunk6_2_checked, root5Node20Step1Chunk6_3_checked, root5Node20Step1Chunk6_4_checked, root5Node20Step1Chunk6_5_checked, root5Node20Step1Chunk7_0_checked, root5Node20Step1Chunk7_1_checked, root5Node20Step1Chunk7_2_checked, root5Node20Step1Chunk7_3_checked, root5Node20Step1Chunk7_4_checked, root5Node20Step1Chunk7_5_checked, root5Node20Step1Chunk8_0_checked, root5Node20Step1Chunk8_1_checked, root5Node20Step1Chunk8_2_checked, root5Node20Step1Chunk8_3_checked, root5Node20Step1Chunk8_4_checked, root5Node20Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node20Domains2 (v : Fin 61) : List State :=
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
  | 26 => [(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(5,1),(5,4),(8,4)]
  | 36 => [(0,1),(6,4)]
  | 37 => [(1,2),(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(1,3),(7,3)]
  | 43 => [(7,5),(8,5)]
  | 44 => [(0,3),(1,0)]
  | 45 => [(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
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
def root5Node20Domains2Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
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
  | 42 => some [(1,3),(7,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(0,3),(1,0)]
  | 45 => some [(7,1),(8,1)]
  | 46 => some [(1,5)]
  | 47 => some [(6,1)]
  | 48 => some [(5,1)]
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
theorem root5Node20Domains2_fast_eq : root5Node20Domains2 = expandDomains root5Node20Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node20Domains2 v = expandDomains root5Node20Domains2Fast v from by decide) v
theorem root5Node20Step2Chunk0_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk0_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk0_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk0_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk0_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk0_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows0_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk1_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows1_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk2_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows2_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk3_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows3_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk4_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows4_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk5_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows5_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk6_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows6_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk7_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows7_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_0_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_0⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_1_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_1⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_2_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_2⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_3_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_3⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_4_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_4⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2Chunk8_5_checked :
    checkNarrowing ⟨table5Scope, table5Rows8_5⟩
      root5Node20Domains1 root5Node20Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains1 root5Node20Domains2
    root5Node20Domains1Fast root5Node20Domains2Fast
    root5Node20Domains1_fast_eq root5Node20Domains2_fast_eq (by decide)
theorem root5Node20Step2_checked :
    checkReplacement table5 root5Node20Domains1 root5Node20Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node20Step2Chunk0_0_checked, root5Node20Step2Chunk0_1_checked, root5Node20Step2Chunk0_2_checked, root5Node20Step2Chunk0_3_checked, root5Node20Step2Chunk0_4_checked, root5Node20Step2Chunk0_5_checked, root5Node20Step2Chunk1_0_checked, root5Node20Step2Chunk1_1_checked, root5Node20Step2Chunk1_2_checked, root5Node20Step2Chunk1_3_checked, root5Node20Step2Chunk1_4_checked, root5Node20Step2Chunk1_5_checked, root5Node20Step2Chunk2_0_checked, root5Node20Step2Chunk2_1_checked, root5Node20Step2Chunk2_2_checked, root5Node20Step2Chunk2_3_checked, root5Node20Step2Chunk2_4_checked, root5Node20Step2Chunk2_5_checked, root5Node20Step2Chunk3_0_checked, root5Node20Step2Chunk3_1_checked, root5Node20Step2Chunk3_2_checked, root5Node20Step2Chunk3_3_checked, root5Node20Step2Chunk3_4_checked, root5Node20Step2Chunk3_5_checked, root5Node20Step2Chunk4_0_checked, root5Node20Step2Chunk4_1_checked, root5Node20Step2Chunk4_2_checked, root5Node20Step2Chunk4_3_checked, root5Node20Step2Chunk4_4_checked, root5Node20Step2Chunk4_5_checked, root5Node20Step2Chunk5_0_checked, root5Node20Step2Chunk5_1_checked, root5Node20Step2Chunk5_2_checked, root5Node20Step2Chunk5_3_checked, root5Node20Step2Chunk5_4_checked, root5Node20Step2Chunk5_5_checked, root5Node20Step2Chunk6_0_checked, root5Node20Step2Chunk6_1_checked, root5Node20Step2Chunk6_2_checked, root5Node20Step2Chunk6_3_checked, root5Node20Step2Chunk6_4_checked, root5Node20Step2Chunk6_5_checked, root5Node20Step2Chunk7_0_checked, root5Node20Step2Chunk7_1_checked, root5Node20Step2Chunk7_2_checked, root5Node20Step2Chunk7_3_checked, root5Node20Step2Chunk7_4_checked, root5Node20Step2Chunk7_5_checked, root5Node20Step2Chunk8_0_checked, root5Node20Step2Chunk8_1_checked, root5Node20Step2Chunk8_2_checked, root5Node20Step2Chunk8_3_checked, root5Node20Step2Chunk8_4_checked, root5Node20Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node20Domains3 (v : Fin 61) : List State :=
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
  | 26 => [(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0)]
  | 33 => [(7,1)]
  | 34 => [(7,5)]
  | 35 => [(5,1),(5,4),(8,4)]
  | 36 => [(0,1),(6,4)]
  | 37 => [(1,2),(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0)]
  | 42 => [(7,3)]
  | 43 => [(7,5),(8,5)]
  | 44 => [(0,3),(1,0)]
  | 45 => [(7,1),(8,1)]
  | 46 => [(1,5)]
  | 47 => [(6,1)]
  | 48 => [(5,1)]
  | 49 => [(0,1)]
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
def root5Node20Domains3Fast (v : Fin 61) : Option (List State) :=
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
  | 26 => some [(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
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
theorem root5Node20Domains3_fast_eq : root5Node20Domains3 = expandDomains root5Node20Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node20Domains3 v = expandDomains root5Node20Domains3Fast v from by decide) v
theorem root5Node20Step3Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root5Node20Domains2 root5Node20Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node20Domains2 root5Node20Domains3
    root5Node20Domains2Fast root5Node20Domains3Fast
    root5Node20Domains2_fast_eq root5Node20Domains3_fast_eq (by decide)
theorem root5Node20Step3_checked :
    checkReplacement table23 root5Node20Domains2 root5Node20Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node20Step3Chunk0_0_checked, root5Node20Step3Chunk0_1_checked, root5Node20Step3Chunk0_2_checked, root5Node20Step3Chunk0_3_checked, root5Node20Step3Chunk0_4_checked, root5Node20Step3Chunk0_5_checked, root5Node20Step3Chunk1_0_checked, root5Node20Step3Chunk1_1_checked, root5Node20Step3Chunk1_2_checked, root5Node20Step3Chunk1_3_checked, root5Node20Step3Chunk1_4_checked, root5Node20Step3Chunk1_5_checked, root5Node20Step3Chunk2_0_checked, root5Node20Step3Chunk2_1_checked, root5Node20Step3Chunk2_2_checked, root5Node20Step3Chunk2_3_checked, root5Node20Step3Chunk2_4_checked, root5Node20Step3Chunk2_5_checked, root5Node20Step3Chunk3_0_checked, root5Node20Step3Chunk3_1_checked, root5Node20Step3Chunk3_2_checked, root5Node20Step3Chunk3_3_checked, root5Node20Step3Chunk3_4_checked, root5Node20Step3Chunk3_5_checked, root5Node20Step3Chunk4_0_checked, root5Node20Step3Chunk4_1_checked, root5Node20Step3Chunk4_2_checked, root5Node20Step3Chunk4_3_checked, root5Node20Step3Chunk4_4_checked, root5Node20Step3Chunk4_5_checked, root5Node20Step3Chunk5_0_checked, root5Node20Step3Chunk5_1_checked, root5Node20Step3Chunk5_2_checked, root5Node20Step3Chunk5_3_checked, root5Node20Step3Chunk5_4_checked, root5Node20Step3Chunk5_5_checked, root5Node20Step3Chunk6_0_checked, root5Node20Step3Chunk6_1_checked, root5Node20Step3Chunk6_2_checked, root5Node20Step3Chunk6_3_checked, root5Node20Step3Chunk6_4_checked, root5Node20Step3Chunk6_5_checked, root5Node20Step3Chunk7_0_checked, root5Node20Step3Chunk7_1_checked, root5Node20Step3Chunk7_2_checked, root5Node20Step3Chunk7_3_checked, root5Node20Step3Chunk7_4_checked, root5Node20Step3Chunk7_5_checked, root5Node20Step3Chunk8_0_checked, root5Node20Step3Chunk8_1_checked, root5Node20Step3Chunk8_2_checked, root5Node20Step3Chunk8_3_checked, root5Node20Step3Chunk8_4_checked, root5Node20Step3Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
