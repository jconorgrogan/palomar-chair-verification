module

public import SpectreFinite.RadiusFourRoot5Part13
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable38
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node42Domains0 : Domains 61 State := restrict root5Node41Domains1 35 (5,4)
def root5Node42Domains0Fast (v : Fin 61) : Option (List State) :=
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
  | 52 => some [(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4),(7,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root5Node42Domains0_fast_eq : root5Node42Domains0 = expandDomains root5Node42Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node42Domains0 v = expandDomains root5Node42Domains0Fast v from by decide) v
def root5Node42Domains1 (v : Fin 61) : List State :=
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
  | 52 => [(5,5),(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(1,4),(3,4)]
  | 57 => [(0,5),(6,3)]
  | 58 => [(4,4),(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(1,3),(6,3)]
def root5Node42Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 52 => some [(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(1,3),(6,3)]
theorem root5Node42Domains1_fast_eq : root5Node42Domains1 = expandDomains root5Node42Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node42Domains1 v = expandDomains root5Node42Domains1Fast v from by decide) v
theorem root5Node42Step1Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root5Node42Domains0 root5Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains0 root5Node42Domains1
    root5Node42Domains0Fast root5Node42Domains1Fast
    root5Node42Domains0_fast_eq root5Node42Domains1_fast_eq (by decide)
theorem root5Node42Step1_checked :
    checkReplacement table35 root5Node42Domains0 root5Node42Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node42Step1Chunk0_0_checked, root5Node42Step1Chunk0_1_checked, root5Node42Step1Chunk0_2_checked, root5Node42Step1Chunk0_3_checked, root5Node42Step1Chunk0_4_checked, root5Node42Step1Chunk0_5_checked, root5Node42Step1Chunk1_0_checked, root5Node42Step1Chunk1_1_checked, root5Node42Step1Chunk1_2_checked, root5Node42Step1Chunk1_3_checked, root5Node42Step1Chunk1_4_checked, root5Node42Step1Chunk1_5_checked, root5Node42Step1Chunk2_0_checked, root5Node42Step1Chunk2_1_checked, root5Node42Step1Chunk2_2_checked, root5Node42Step1Chunk2_3_checked, root5Node42Step1Chunk2_4_checked, root5Node42Step1Chunk2_5_checked, root5Node42Step1Chunk3_0_checked, root5Node42Step1Chunk3_1_checked, root5Node42Step1Chunk3_2_checked, root5Node42Step1Chunk3_3_checked, root5Node42Step1Chunk3_4_checked, root5Node42Step1Chunk3_5_checked, root5Node42Step1Chunk4_0_checked, root5Node42Step1Chunk4_1_checked, root5Node42Step1Chunk4_2_checked, root5Node42Step1Chunk4_3_checked, root5Node42Step1Chunk4_4_checked, root5Node42Step1Chunk4_5_checked, root5Node42Step1Chunk5_0_checked, root5Node42Step1Chunk5_1_checked, root5Node42Step1Chunk5_2_checked, root5Node42Step1Chunk5_3_checked, root5Node42Step1Chunk5_4_checked, root5Node42Step1Chunk5_5_checked, root5Node42Step1Chunk6_0_checked, root5Node42Step1Chunk6_1_checked, root5Node42Step1Chunk6_2_checked, root5Node42Step1Chunk6_3_checked, root5Node42Step1Chunk6_4_checked, root5Node42Step1Chunk6_5_checked, root5Node42Step1Chunk7_0_checked, root5Node42Step1Chunk7_1_checked, root5Node42Step1Chunk7_2_checked, root5Node42Step1Chunk7_3_checked, root5Node42Step1Chunk7_4_checked, root5Node42Step1Chunk7_5_checked, root5Node42Step1Chunk8_0_checked, root5Node42Step1Chunk8_1_checked, root5Node42Step1Chunk8_2_checked, root5Node42Step1Chunk8_3_checked, root5Node42Step1Chunk8_4_checked, root5Node42Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node42Domains2 (v : Fin 61) : List State :=
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
  | 52 => [(5,5),(8,5)]
  | 53 => [(7,0)]
  | 54 => [(8,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(1,4),(3,4)]
  | 57 => [(0,5),(6,3)]
  | 58 => [(4,4),(7,2)]
  | 59 => [(1,4),(7,4)]
  | _ => [(0,5),(6,3)]
def root5Node42Domains2Fast (v : Fin 61) : Option (List State) :=
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
  | 52 => some [(5,5),(8,5)]
  | 53 => some [(7,0)]
  | 54 => some [(8,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(1,4),(3,4)]
  | 57 => some [(0,5),(6,3)]
  | 58 => some [(4,4),(7,2)]
  | 59 => some [(1,4),(7,4)]
  | _ => some [(0,5),(6,3)]
theorem root5Node42Domains2_fast_eq : root5Node42Domains2 = expandDomains root5Node42Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node42Domains2 v = expandDomains root5Node42Domains2Fast v from by decide) v
theorem root5Node42Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root5Node42Domains1 root5Node42Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node42Domains1 root5Node42Domains2
    root5Node42Domains1Fast root5Node42Domains2Fast
    root5Node42Domains1_fast_eq root5Node42Domains2_fast_eq (by decide)
theorem root5Node42Step2_checked :
    checkReplacement table46 root5Node42Domains1 root5Node42Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node42Step2Chunk0_0_checked, root5Node42Step2Chunk0_1_checked, root5Node42Step2Chunk0_2_checked, root5Node42Step2Chunk0_3_checked, root5Node42Step2Chunk0_4_checked, root5Node42Step2Chunk0_5_checked, root5Node42Step2Chunk1_0_checked, root5Node42Step2Chunk1_1_checked, root5Node42Step2Chunk1_2_checked, root5Node42Step2Chunk1_3_checked, root5Node42Step2Chunk1_4_checked, root5Node42Step2Chunk1_5_checked, root5Node42Step2Chunk2_0_checked, root5Node42Step2Chunk2_1_checked, root5Node42Step2Chunk2_2_checked, root5Node42Step2Chunk2_3_checked, root5Node42Step2Chunk2_4_checked, root5Node42Step2Chunk2_5_checked, root5Node42Step2Chunk3_0_checked, root5Node42Step2Chunk3_1_checked, root5Node42Step2Chunk3_2_checked, root5Node42Step2Chunk3_3_checked, root5Node42Step2Chunk3_4_checked, root5Node42Step2Chunk3_5_checked, root5Node42Step2Chunk4_0_checked, root5Node42Step2Chunk4_1_checked, root5Node42Step2Chunk4_2_checked, root5Node42Step2Chunk4_3_checked, root5Node42Step2Chunk4_4_checked, root5Node42Step2Chunk4_5_checked, root5Node42Step2Chunk5_0_checked, root5Node42Step2Chunk5_1_checked, root5Node42Step2Chunk5_2_checked, root5Node42Step2Chunk5_3_checked, root5Node42Step2Chunk5_4_checked, root5Node42Step2Chunk5_5_checked, root5Node42Step2Chunk6_0_checked, root5Node42Step2Chunk6_1_checked, root5Node42Step2Chunk6_2_checked, root5Node42Step2Chunk6_3_checked, root5Node42Step2Chunk6_4_checked, root5Node42Step2Chunk6_5_checked, root5Node42Step2Chunk7_0_checked, root5Node42Step2Chunk7_1_checked, root5Node42Step2Chunk7_2_checked, root5Node42Step2Chunk7_3_checked, root5Node42Step2Chunk7_4_checked, root5Node42Step2Chunk7_5_checked, root5Node42Step2Chunk8_0_checked, root5Node42Step2Chunk8_1_checked, root5Node42Step2Chunk8_2_checked, root5Node42Step2Chunk8_3_checked, root5Node42Step2Chunk8_4_checked, root5Node42Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node43Domains0 : Domains 61 State := restrict root5Node42Domains2 52 (5,5)
def root5Node43Domains0Fast (v : Fin 61) : Option (List State) :=
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
theorem root5Node43Domains0_fast_eq : root5Node43Domains0 = expandDomains root5Node43Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node43Domains0 v = expandDomains root5Node43Domains0Fast v from by decide) v
def root5Node43Domains1 (v : Fin 61) : List State :=
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
def root5Node43Domains1Fast (v : Fin 61) : Option (List State) :=
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
theorem root5Node43Domains1_fast_eq : root5Node43Domains1 = expandDomains root5Node43Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node43Domains1 v = expandDomains root5Node43Domains1Fast v from by decide) v
theorem root5Node43Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root5Node43Domains0 root5Node43Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node43Domains0 root5Node43Domains1
    root5Node43Domains0Fast root5Node43Domains1Fast
    root5Node43Domains0_fast_eq root5Node43Domains1_fast_eq (by decide)
theorem root5Node43Step1_checked :
    checkReplacement table46 root5Node43Domains0 root5Node43Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node43Step1Chunk0_0_checked, root5Node43Step1Chunk0_1_checked, root5Node43Step1Chunk0_2_checked, root5Node43Step1Chunk0_3_checked, root5Node43Step1Chunk0_4_checked, root5Node43Step1Chunk0_5_checked, root5Node43Step1Chunk1_0_checked, root5Node43Step1Chunk1_1_checked, root5Node43Step1Chunk1_2_checked, root5Node43Step1Chunk1_3_checked, root5Node43Step1Chunk1_4_checked, root5Node43Step1Chunk1_5_checked, root5Node43Step1Chunk2_0_checked, root5Node43Step1Chunk2_1_checked, root5Node43Step1Chunk2_2_checked, root5Node43Step1Chunk2_3_checked, root5Node43Step1Chunk2_4_checked, root5Node43Step1Chunk2_5_checked, root5Node43Step1Chunk3_0_checked, root5Node43Step1Chunk3_1_checked, root5Node43Step1Chunk3_2_checked, root5Node43Step1Chunk3_3_checked, root5Node43Step1Chunk3_4_checked, root5Node43Step1Chunk3_5_checked, root5Node43Step1Chunk4_0_checked, root5Node43Step1Chunk4_1_checked, root5Node43Step1Chunk4_2_checked, root5Node43Step1Chunk4_3_checked, root5Node43Step1Chunk4_4_checked, root5Node43Step1Chunk4_5_checked, root5Node43Step1Chunk5_0_checked, root5Node43Step1Chunk5_1_checked, root5Node43Step1Chunk5_2_checked, root5Node43Step1Chunk5_3_checked, root5Node43Step1Chunk5_4_checked, root5Node43Step1Chunk5_5_checked, root5Node43Step1Chunk6_0_checked, root5Node43Step1Chunk6_1_checked, root5Node43Step1Chunk6_2_checked, root5Node43Step1Chunk6_3_checked, root5Node43Step1Chunk6_4_checked, root5Node43Step1Chunk6_5_checked, root5Node43Step1Chunk7_0_checked, root5Node43Step1Chunk7_1_checked, root5Node43Step1Chunk7_2_checked, root5Node43Step1Chunk7_3_checked, root5Node43Step1Chunk7_4_checked, root5Node43Step1Chunk7_5_checked, root5Node43Step1Chunk8_0_checked, root5Node43Step1Chunk8_1_checked, root5Node43Step1Chunk8_2_checked, root5Node43Step1Chunk8_3_checked, root5Node43Step1Chunk8_4_checked, root5Node43Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node43Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node43Domains1 (.output 20) = true := by decide
def root5Node44Domains0 : Domains 61 State := restrict root5Node42Domains2 52 (8,5)
def root5Node44Domains0Fast (v : Fin 61) : Option (List State) :=
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
theorem root5Node44Domains0_fast_eq : root5Node44Domains0 = expandDomains root5Node44Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node44Domains0 v = expandDomains root5Node44Domains0Fast v from by decide) v
def root5Node44Domains1 (v : Fin 61) : List State :=
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
def root5Node44Domains1Fast (v : Fin 61) : Option (List State) :=
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
theorem root5Node44Domains1_fast_eq : root5Node44Domains1 = expandDomains root5Node44Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node44Domains1 v = expandDomains root5Node44Domains1Fast v from by decide) v
theorem root5Node44Step1Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root5Node44Domains0 root5Node44Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node44Domains0 root5Node44Domains1
    root5Node44Domains0Fast root5Node44Domains1Fast
    root5Node44Domains0_fast_eq root5Node44Domains1_fast_eq (by decide)
theorem root5Node44Step1_checked :
    checkReplacement table46 root5Node44Domains0 root5Node44Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node44Step1Chunk0_0_checked, root5Node44Step1Chunk0_1_checked, root5Node44Step1Chunk0_2_checked, root5Node44Step1Chunk0_3_checked, root5Node44Step1Chunk0_4_checked, root5Node44Step1Chunk0_5_checked, root5Node44Step1Chunk1_0_checked, root5Node44Step1Chunk1_1_checked, root5Node44Step1Chunk1_2_checked, root5Node44Step1Chunk1_3_checked, root5Node44Step1Chunk1_4_checked, root5Node44Step1Chunk1_5_checked, root5Node44Step1Chunk2_0_checked, root5Node44Step1Chunk2_1_checked, root5Node44Step1Chunk2_2_checked, root5Node44Step1Chunk2_3_checked, root5Node44Step1Chunk2_4_checked, root5Node44Step1Chunk2_5_checked, root5Node44Step1Chunk3_0_checked, root5Node44Step1Chunk3_1_checked, root5Node44Step1Chunk3_2_checked, root5Node44Step1Chunk3_3_checked, root5Node44Step1Chunk3_4_checked, root5Node44Step1Chunk3_5_checked, root5Node44Step1Chunk4_0_checked, root5Node44Step1Chunk4_1_checked, root5Node44Step1Chunk4_2_checked, root5Node44Step1Chunk4_3_checked, root5Node44Step1Chunk4_4_checked, root5Node44Step1Chunk4_5_checked, root5Node44Step1Chunk5_0_checked, root5Node44Step1Chunk5_1_checked, root5Node44Step1Chunk5_2_checked, root5Node44Step1Chunk5_3_checked, root5Node44Step1Chunk5_4_checked, root5Node44Step1Chunk5_5_checked, root5Node44Step1Chunk6_0_checked, root5Node44Step1Chunk6_1_checked, root5Node44Step1Chunk6_2_checked, root5Node44Step1Chunk6_3_checked, root5Node44Step1Chunk6_4_checked, root5Node44Step1Chunk6_5_checked, root5Node44Step1Chunk7_0_checked, root5Node44Step1Chunk7_1_checked, root5Node44Step1Chunk7_2_checked, root5Node44Step1Chunk7_3_checked, root5Node44Step1Chunk7_4_checked, root5Node44Step1Chunk7_5_checked, root5Node44Step1Chunk8_0_checked, root5Node44Step1Chunk8_1_checked, root5Node44Step1Chunk8_2_checked, root5Node44Step1Chunk8_3_checked, root5Node44Step1Chunk8_4_checked, root5Node44Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root5Node44Leaf_checked :
    checkCover 1 constraints root5Outputs root5Node44Domains1 (.output 21) = true := by decide
def root5Node45Domains0 : Domains 61 State := restrict root5Node41Domains1 35 (8,4)
def root5Node45Domains0Fast (v : Fin 61) : Option (List State) :=
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
theorem root5Node45Domains0_fast_eq : root5Node45Domains0 = expandDomains root5Node45Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node45Domains0 v = expandDomains root5Node45Domains0Fast v from by decide) v
def root5Node45Domains1 (v : Fin 61) : List State :=
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
def root5Node45Domains1Fast (v : Fin 61) : Option (List State) :=
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
theorem root5Node45Domains1_fast_eq : root5Node45Domains1 = expandDomains root5Node45Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node45Domains1 v = expandDomains root5Node45Domains1Fast v from by decide) v
theorem root5Node45Step1Chunk0_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk0_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk0_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk0_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk0_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk0_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk1_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk2_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk3_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk4_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk5_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk6_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk7_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_0⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_1⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_2⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_3⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_4⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1Chunk8_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_5⟩
      root5Node45Domains0 root5Node45Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node45Domains0 root5Node45Domains1
    root5Node45Domains0Fast root5Node45Domains1Fast
    root5Node45Domains0_fast_eq root5Node45Domains1_fast_eq (by decide)
theorem root5Node45Step1_checked :
    checkReplacement table38 root5Node45Domains0 root5Node45Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node45Step1Chunk0_0_checked, root5Node45Step1Chunk0_1_checked, root5Node45Step1Chunk0_2_checked, root5Node45Step1Chunk0_3_checked, root5Node45Step1Chunk0_4_checked, root5Node45Step1Chunk0_5_checked, root5Node45Step1Chunk1_0_checked, root5Node45Step1Chunk1_1_checked, root5Node45Step1Chunk1_2_checked, root5Node45Step1Chunk1_3_checked, root5Node45Step1Chunk1_4_checked, root5Node45Step1Chunk1_5_checked, root5Node45Step1Chunk2_0_checked, root5Node45Step1Chunk2_1_checked, root5Node45Step1Chunk2_2_checked, root5Node45Step1Chunk2_3_checked, root5Node45Step1Chunk2_4_checked, root5Node45Step1Chunk2_5_checked, root5Node45Step1Chunk3_0_checked, root5Node45Step1Chunk3_1_checked, root5Node45Step1Chunk3_2_checked, root5Node45Step1Chunk3_3_checked, root5Node45Step1Chunk3_4_checked, root5Node45Step1Chunk3_5_checked, root5Node45Step1Chunk4_0_checked, root5Node45Step1Chunk4_1_checked, root5Node45Step1Chunk4_2_checked, root5Node45Step1Chunk4_3_checked, root5Node45Step1Chunk4_4_checked, root5Node45Step1Chunk4_5_checked, root5Node45Step1Chunk5_0_checked, root5Node45Step1Chunk5_1_checked, root5Node45Step1Chunk5_2_checked, root5Node45Step1Chunk5_3_checked, root5Node45Step1Chunk5_4_checked, root5Node45Step1Chunk5_5_checked, root5Node45Step1Chunk6_0_checked, root5Node45Step1Chunk6_1_checked, root5Node45Step1Chunk6_2_checked, root5Node45Step1Chunk6_3_checked, root5Node45Step1Chunk6_4_checked, root5Node45Step1Chunk6_5_checked, root5Node45Step1Chunk7_0_checked, root5Node45Step1Chunk7_1_checked, root5Node45Step1Chunk7_2_checked, root5Node45Step1Chunk7_3_checked, root5Node45Step1Chunk7_4_checked, root5Node45Step1Chunk7_5_checked, root5Node45Step1Chunk8_0_checked, root5Node45Step1Chunk8_1_checked, root5Node45Step1Chunk8_2_checked, root5Node45Step1Chunk8_3_checked, root5Node45Step1Chunk8_4_checked, root5Node45Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
