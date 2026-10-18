module

public import SpectreFinite.RadiusFourRoot7Part30
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable0
public import SpectreFinite.RadiusFourTable11
public import SpectreFinite.RadiusFourTable19
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node93Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5),(6,5),(7,5)]
  | 1 => [(0,3),(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(4,5),(7,3),(8,5)]
  | 6 => [(4,2),(7,0)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0),(6,3),(6,4)]
  | 12 => [(1,2),(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(0,2),(1,5),(7,5)]
  | 19 => [(0,3),(1,1),(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(0,0),(6,4)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => [(4,2),(7,0),(8,0)]
  | 28 => [(5,3),(8,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(1,5),(3,5),(7,5)]
  | 33 => [(0,3),(6,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => [(1,4),(3,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,2)]
  | 42 => [(1,3),(3,3),(5,3),(7,3)]
  | 43 => [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(6,5)]
  | 50 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(7,0)]
  | 55 => [(2,3),(2,5),(4,5)]
  | 56 => [(5,1),(5,4),(8,4)]
  | 57 => [(0,1),(1,4),(6,4)]
  | 58 => [(0,5),(1,2),(6,2)]
  | 59 => [(4,4),(8,4)]
  | _ => [(0,0),(6,4)]
def root7Node93Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5),(6,5),(7,5)]
  | 1 => some [(0,3),(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5),(7,3),(8,5)]
  | 6 => some [(4,2),(7,0)]
  | 7 => some [(5,3),(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0),(6,3),(6,4)]
  | 12 => some [(1,2),(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(0,2),(1,5),(7,5)]
  | 19 => some [(0,3),(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => some [(4,2),(7,0),(8,0)]
  | 28 => some [(5,3),(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => some [(1,4),(3,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node93Domains2_fast_eq : root7Node93Domains2 = expandDomains root7Node93Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node93Domains2 v = expandDomains root7Node93Domains2Fast v from by decide) v
theorem root7Node93Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node93Domains1 root7Node93Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains1 root7Node93Domains2
    root7Node93Domains1Fast root7Node93Domains2Fast
    root7Node93Domains1_fast_eq root7Node93Domains2_fast_eq (by decide)
theorem root7Node93Step2_checked :
    checkReplacement table39 root7Node93Domains1 root7Node93Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node93Step2Chunk0_0_checked, root7Node93Step2Chunk0_1_checked, root7Node93Step2Chunk0_2_checked, root7Node93Step2Chunk0_3_checked, root7Node93Step2Chunk0_4_checked, root7Node93Step2Chunk0_5_checked, root7Node93Step2Chunk1_0_checked, root7Node93Step2Chunk1_1_checked, root7Node93Step2Chunk1_2_checked, root7Node93Step2Chunk1_3_checked, root7Node93Step2Chunk1_4_checked, root7Node93Step2Chunk1_5_checked, root7Node93Step2Chunk2_0_checked, root7Node93Step2Chunk2_1_checked, root7Node93Step2Chunk2_2_checked, root7Node93Step2Chunk2_3_checked, root7Node93Step2Chunk2_4_checked, root7Node93Step2Chunk2_5_checked, root7Node93Step2Chunk3_0_checked, root7Node93Step2Chunk3_1_checked, root7Node93Step2Chunk3_2_checked, root7Node93Step2Chunk3_3_checked, root7Node93Step2Chunk3_4_checked, root7Node93Step2Chunk3_5_checked, root7Node93Step2Chunk4_0_checked, root7Node93Step2Chunk4_1_checked, root7Node93Step2Chunk4_2_checked, root7Node93Step2Chunk4_3_checked, root7Node93Step2Chunk4_4_checked, root7Node93Step2Chunk4_5_checked, root7Node93Step2Chunk5_0_checked, root7Node93Step2Chunk5_1_checked, root7Node93Step2Chunk5_2_checked, root7Node93Step2Chunk5_3_checked, root7Node93Step2Chunk5_4_checked, root7Node93Step2Chunk5_5_checked, root7Node93Step2Chunk6_0_checked, root7Node93Step2Chunk6_1_checked, root7Node93Step2Chunk6_2_checked, root7Node93Step2Chunk6_3_checked, root7Node93Step2Chunk6_4_checked, root7Node93Step2Chunk6_5_checked, root7Node93Step2Chunk7_0_checked, root7Node93Step2Chunk7_1_checked, root7Node93Step2Chunk7_2_checked, root7Node93Step2Chunk7_3_checked, root7Node93Step2Chunk7_4_checked, root7Node93Step2Chunk7_5_checked, root7Node93Step2Chunk8_0_checked, root7Node93Step2Chunk8_1_checked, root7Node93Step2Chunk8_2_checked, root7Node93Step2Chunk8_3_checked, root7Node93Step2Chunk8_4_checked, root7Node93Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node93Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5),(7,5)]
  | 1 => [(0,3),(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(4,5),(7,3),(8,5)]
  | 6 => [(4,2),(7,0)]
  | 7 => [(5,3),(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0),(6,3),(6,4)]
  | 12 => [(1,2),(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(0,2),(1,5),(7,5)]
  | 19 => [(0,3),(1,1),(6,1)]
  | 20 => [(8,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(0,0),(6,4)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => [(4,2),(7,0),(8,0)]
  | 28 => [(5,3),(8,3)]
  | 29 => [(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(1,5),(3,5),(7,5)]
  | 33 => [(0,3),(6,1)]
  | 34 => [(4,1),(8,1)]
  | 35 => [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => [(1,4),(3,4),(7,4)]
  | 37 => [(0,5),(6,3)]
  | 38 => [(4,4),(7,2)]
  | 39 => [(1,4),(7,4)]
  | 40 => [(0,5),(1,3),(6,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,2)]
  | 42 => [(1,3),(3,3),(5,3),(7,3)]
  | 43 => [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 44 => [(0,2),(6,0)]
  | 45 => [(1,1),(7,1)]
  | 46 => [(4,1),(7,5),(8,1)]
  | 47 => [(0,2),(6,0),(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(6,5)]
  | 50 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(7,0)]
  | 55 => [(2,3),(2,5),(4,5)]
  | 56 => [(5,1),(5,4),(8,4)]
  | 57 => [(0,1),(1,4),(6,4)]
  | 58 => [(0,5),(1,2),(6,2)]
  | 59 => [(4,4),(8,4)]
  | _ => [(0,0),(6,4)]
def root7Node93Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5),(7,5)]
  | 1 => some [(0,3),(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5),(7,3),(8,5)]
  | 6 => some [(4,2),(7,0)]
  | 7 => some [(5,3),(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0),(6,3),(6,4)]
  | 12 => some [(1,2),(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(0,2),(1,5),(7,5)]
  | 19 => some [(0,3),(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => some [(4,2),(7,0),(8,0)]
  | 28 => some [(5,3),(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => some [(1,4),(3,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node93Domains3_fast_eq : root7Node93Domains3 = expandDomains root7Node93Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node93Domains3 v = expandDomains root7Node93Domains3Fast v from by decide) v
theorem root7Node93Step3Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root7Node93Domains2 root7Node93Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node93Domains2 root7Node93Domains3
    root7Node93Domains2Fast root7Node93Domains3Fast
    root7Node93Domains2_fast_eq root7Node93Domains3_fast_eq (by decide)
theorem root7Node93Step3_checked :
    checkReplacement table0 root7Node93Domains2 root7Node93Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node93Step3Chunk0_0_checked, root7Node93Step3Chunk0_1_checked, root7Node93Step3Chunk0_2_checked, root7Node93Step3Chunk0_3_checked, root7Node93Step3Chunk0_4_checked, root7Node93Step3Chunk0_5_checked, root7Node93Step3Chunk1_0_checked, root7Node93Step3Chunk1_1_checked, root7Node93Step3Chunk1_2_checked, root7Node93Step3Chunk1_3_checked, root7Node93Step3Chunk1_4_checked, root7Node93Step3Chunk1_5_checked, root7Node93Step3Chunk2_0_checked, root7Node93Step3Chunk2_1_checked, root7Node93Step3Chunk2_2_checked, root7Node93Step3Chunk2_3_checked, root7Node93Step3Chunk2_4_checked, root7Node93Step3Chunk2_5_checked, root7Node93Step3Chunk3_0_checked, root7Node93Step3Chunk3_1_checked, root7Node93Step3Chunk3_2_checked, root7Node93Step3Chunk3_3_checked, root7Node93Step3Chunk3_4_checked, root7Node93Step3Chunk3_5_checked, root7Node93Step3Chunk4_0_checked, root7Node93Step3Chunk4_1_checked, root7Node93Step3Chunk4_2_checked, root7Node93Step3Chunk4_3_checked, root7Node93Step3Chunk4_4_checked, root7Node93Step3Chunk4_5_checked, root7Node93Step3Chunk5_0_checked, root7Node93Step3Chunk5_1_checked, root7Node93Step3Chunk5_2_checked, root7Node93Step3Chunk5_3_checked, root7Node93Step3Chunk5_4_checked, root7Node93Step3Chunk5_5_checked, root7Node93Step3Chunk6_0_checked, root7Node93Step3Chunk6_1_checked, root7Node93Step3Chunk6_2_checked, root7Node93Step3Chunk6_3_checked, root7Node93Step3Chunk6_4_checked, root7Node93Step3Chunk6_5_checked, root7Node93Step3Chunk7_0_checked, root7Node93Step3Chunk7_1_checked, root7Node93Step3Chunk7_2_checked, root7Node93Step3Chunk7_3_checked, root7Node93Step3Chunk7_4_checked, root7Node93Step3Chunk7_5_checked, root7Node93Step3Chunk8_0_checked, root7Node93Step3Chunk8_1_checked, root7Node93Step3Chunk8_2_checked, root7Node93Step3Chunk8_3_checked, root7Node93Step3Chunk8_4_checked, root7Node93Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node94Domains0 : Domains 61 State := restrict root7Node93Domains3 0 (1,5)
def root7Node94Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(0,3),(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5),(7,3),(8,5)]
  | 6 => some [(4,2),(7,0)]
  | 7 => some [(5,3),(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0),(6,3),(6,4)]
  | 12 => some [(1,2),(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(0,2),(1,5),(7,5)]
  | 19 => some [(0,3),(1,1),(6,1)]
  | 20 => some [(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => some [(4,2),(7,0),(8,0)]
  | 28 => some [(5,3),(8,3)]
  | 29 => some [(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(4,1),(8,1)]
  | 35 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => some [(1,4),(3,4),(7,4)]
  | 37 => some [(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(7,4)]
  | 40 => some [(0,5),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,2)]
  | 42 => some [(1,3),(3,3),(5,3),(7,3)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1),(7,5)]
  | 44 => some [(0,2),(6,0)]
  | 45 => some [(1,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(6,5)]
  | 50 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node94Domains0_fast_eq : root7Node94Domains0 = expandDomains root7Node94Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node94Domains0 v = expandDomains root7Node94Domains0Fast v from by decide) v
def root7Node94Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
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
  | 50 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => [(4,0),(8,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(7,0)]
  | 55 => [(2,3),(2,5),(4,5)]
  | 56 => [(5,1),(5,4),(8,4)]
  | 57 => [(0,1),(1,4),(6,4)]
  | 58 => [(0,5),(1,2),(6,2)]
  | 59 => [(4,4),(8,4)]
  | _ => [(0,0),(6,4)]
def root7Node94Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
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
  | 50 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 51 => some [(4,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,1),(5,4),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4)]
  | 58 => some [(0,5),(1,2),(6,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node94Domains1_fast_eq : root7Node94Domains1 = expandDomains root7Node94Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node94Domains1 v = expandDomains root7Node94Domains1Fast v from by decide) v
theorem root7Node94Step1Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root7Node94Domains0 root7Node94Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains0 root7Node94Domains1
    root7Node94Domains0Fast root7Node94Domains1Fast
    root7Node94Domains0_fast_eq root7Node94Domains1_fast_eq (by decide)
theorem root7Node94Step1_checked :
    checkReplacement table19 root7Node94Domains0 root7Node94Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node94Step1Chunk0_0_checked, root7Node94Step1Chunk0_1_checked, root7Node94Step1Chunk0_2_checked, root7Node94Step1Chunk0_3_checked, root7Node94Step1Chunk0_4_checked, root7Node94Step1Chunk0_5_checked, root7Node94Step1Chunk1_0_checked, root7Node94Step1Chunk1_1_checked, root7Node94Step1Chunk1_2_checked, root7Node94Step1Chunk1_3_checked, root7Node94Step1Chunk1_4_checked, root7Node94Step1Chunk1_5_checked, root7Node94Step1Chunk2_0_checked, root7Node94Step1Chunk2_1_checked, root7Node94Step1Chunk2_2_checked, root7Node94Step1Chunk2_3_checked, root7Node94Step1Chunk2_4_checked, root7Node94Step1Chunk2_5_checked, root7Node94Step1Chunk3_0_checked, root7Node94Step1Chunk3_1_checked, root7Node94Step1Chunk3_2_checked, root7Node94Step1Chunk3_3_checked, root7Node94Step1Chunk3_4_checked, root7Node94Step1Chunk3_5_checked, root7Node94Step1Chunk4_0_checked, root7Node94Step1Chunk4_1_checked, root7Node94Step1Chunk4_2_checked, root7Node94Step1Chunk4_3_checked, root7Node94Step1Chunk4_4_checked, root7Node94Step1Chunk4_5_checked, root7Node94Step1Chunk5_0_checked, root7Node94Step1Chunk5_1_checked, root7Node94Step1Chunk5_2_checked, root7Node94Step1Chunk5_3_checked, root7Node94Step1Chunk5_4_checked, root7Node94Step1Chunk5_5_checked, root7Node94Step1Chunk6_0_checked, root7Node94Step1Chunk6_1_checked, root7Node94Step1Chunk6_2_checked, root7Node94Step1Chunk6_3_checked, root7Node94Step1Chunk6_4_checked, root7Node94Step1Chunk6_5_checked, root7Node94Step1Chunk7_0_checked, root7Node94Step1Chunk7_1_checked, root7Node94Step1Chunk7_2_checked, root7Node94Step1Chunk7_3_checked, root7Node94Step1Chunk7_4_checked, root7Node94Step1Chunk7_5_checked, root7Node94Step1Chunk8_0_checked, root7Node94Step1Chunk8_1_checked, root7Node94Step1Chunk8_2_checked, root7Node94Step1Chunk8_3_checked, root7Node94Step1Chunk8_4_checked, root7Node94Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node94Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(4,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0),(6,3)]
  | 12 => [(7,2)]
  | 13 => [(7,4)]
  | 14 => [(1,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(0,2),(1,5)]
  | 19 => [(1,1),(6,1)]
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
  | 53 => [(5,2),(5,5),(8,2)]
  | 54 => [(3,0),(5,0),(7,0)]
  | 55 => [(2,3),(2,5),(4,5)]
  | 56 => [(5,4),(8,4)]
  | 57 => [(1,4),(6,4)]
  | 58 => [(0,5),(1,2)]
  | 59 => [(4,4),(8,4)]
  | _ => [(0,0),(6,4)]
def root7Node94Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
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
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node94Domains2_fast_eq : root7Node94Domains2 = expandDomains root7Node94Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node94Domains2 v = expandDomains root7Node94Domains2Fast v from by decide) v
theorem root7Node94Step2Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root7Node94Domains1 root7Node94Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node94Domains1 root7Node94Domains2
    root7Node94Domains1Fast root7Node94Domains2Fast
    root7Node94Domains1_fast_eq root7Node94Domains2_fast_eq (by decide)
theorem root7Node94Step2_checked :
    checkReplacement table37 root7Node94Domains1 root7Node94Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node94Step2Chunk0_0_checked, root7Node94Step2Chunk0_1_checked, root7Node94Step2Chunk0_2_checked, root7Node94Step2Chunk0_3_checked, root7Node94Step2Chunk0_4_checked, root7Node94Step2Chunk0_5_checked, root7Node94Step2Chunk1_0_checked, root7Node94Step2Chunk1_1_checked, root7Node94Step2Chunk1_2_checked, root7Node94Step2Chunk1_3_checked, root7Node94Step2Chunk1_4_checked, root7Node94Step2Chunk1_5_checked, root7Node94Step2Chunk2_0_checked, root7Node94Step2Chunk2_1_checked, root7Node94Step2Chunk2_2_checked, root7Node94Step2Chunk2_3_checked, root7Node94Step2Chunk2_4_checked, root7Node94Step2Chunk2_5_checked, root7Node94Step2Chunk3_0_checked, root7Node94Step2Chunk3_1_checked, root7Node94Step2Chunk3_2_checked, root7Node94Step2Chunk3_3_checked, root7Node94Step2Chunk3_4_checked, root7Node94Step2Chunk3_5_checked, root7Node94Step2Chunk4_0_checked, root7Node94Step2Chunk4_1_checked, root7Node94Step2Chunk4_2_checked, root7Node94Step2Chunk4_3_checked, root7Node94Step2Chunk4_4_checked, root7Node94Step2Chunk4_5_checked, root7Node94Step2Chunk5_0_checked, root7Node94Step2Chunk5_1_checked, root7Node94Step2Chunk5_2_checked, root7Node94Step2Chunk5_3_checked, root7Node94Step2Chunk5_4_checked, root7Node94Step2Chunk5_5_checked, root7Node94Step2Chunk6_0_checked, root7Node94Step2Chunk6_1_checked, root7Node94Step2Chunk6_2_checked, root7Node94Step2Chunk6_3_checked, root7Node94Step2Chunk6_4_checked, root7Node94Step2Chunk6_5_checked, root7Node94Step2Chunk7_0_checked, root7Node94Step2Chunk7_1_checked, root7Node94Step2Chunk7_2_checked, root7Node94Step2Chunk7_3_checked, root7Node94Step2Chunk7_4_checked, root7Node94Step2Chunk7_5_checked, root7Node94Step2Chunk8_0_checked, root7Node94Step2Chunk8_1_checked, root7Node94Step2Chunk8_2_checked, root7Node94Step2Chunk8_3_checked, root7Node94Step2Chunk8_4_checked, root7Node94Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node95Domains0 : Domains 61 State := restrict root7Node94Domains2 5 (4,5)
def root7Node95Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0),(6,3)]
  | 12 => some [(7,2)]
  | 13 => some [(7,4)]
  | 14 => some [(1,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(0,2),(1,5)]
  | 19 => some [(1,1),(6,1)]
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
  | 53 => some [(5,2),(5,5),(8,2)]
  | 54 => some [(3,0),(5,0),(7,0)]
  | 55 => some [(2,3),(2,5),(4,5)]
  | 56 => some [(5,4),(8,4)]
  | 57 => some [(1,4),(6,4)]
  | 58 => some [(0,5),(1,2)]
  | 59 => some [(4,4),(8,4)]
  | _ => some [(0,0),(6,4)]
theorem root7Node95Domains0_fast_eq : root7Node95Domains0 = expandDomains root7Node95Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node95Domains0 v = expandDomains root7Node95Domains0Fast v from by decide) v
def root7Node95Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1)]
  | 3 => [(0,1)]
  | 4 => [(6,2)]
  | 5 => [(4,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(8,5)]
  | 9 => [(1,0)]
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
def root7Node95Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1)]
  | 3 => some [(0,1)]
  | 4 => some [(6,2)]
  | 5 => some [(4,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(8,5)]
  | 9 => some [(1,0)]
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
theorem root7Node95Domains1_fast_eq : root7Node95Domains1 = expandDomains root7Node95Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node95Domains1 v = expandDomains root7Node95Domains1Fast v from by decide) v
theorem root7Node95Step1Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root7Node95Domains0 root7Node95Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node95Domains0 root7Node95Domains1
    root7Node95Domains0Fast root7Node95Domains1Fast
    root7Node95Domains0_fast_eq root7Node95Domains1_fast_eq (by decide)
theorem root7Node95Step1_checked :
    checkReplacement table11 root7Node95Domains0 root7Node95Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node95Step1Chunk0_0_checked, root7Node95Step1Chunk0_1_checked, root7Node95Step1Chunk0_2_checked, root7Node95Step1Chunk0_3_checked, root7Node95Step1Chunk0_4_checked, root7Node95Step1Chunk0_5_checked, root7Node95Step1Chunk1_0_checked, root7Node95Step1Chunk1_1_checked, root7Node95Step1Chunk1_2_checked, root7Node95Step1Chunk1_3_checked, root7Node95Step1Chunk1_4_checked, root7Node95Step1Chunk1_5_checked, root7Node95Step1Chunk2_0_checked, root7Node95Step1Chunk2_1_checked, root7Node95Step1Chunk2_2_checked, root7Node95Step1Chunk2_3_checked, root7Node95Step1Chunk2_4_checked, root7Node95Step1Chunk2_5_checked, root7Node95Step1Chunk3_0_checked, root7Node95Step1Chunk3_1_checked, root7Node95Step1Chunk3_2_checked, root7Node95Step1Chunk3_3_checked, root7Node95Step1Chunk3_4_checked, root7Node95Step1Chunk3_5_checked, root7Node95Step1Chunk4_0_checked, root7Node95Step1Chunk4_1_checked, root7Node95Step1Chunk4_2_checked, root7Node95Step1Chunk4_3_checked, root7Node95Step1Chunk4_4_checked, root7Node95Step1Chunk4_5_checked, root7Node95Step1Chunk5_0_checked, root7Node95Step1Chunk5_1_checked, root7Node95Step1Chunk5_2_checked, root7Node95Step1Chunk5_3_checked, root7Node95Step1Chunk5_4_checked, root7Node95Step1Chunk5_5_checked, root7Node95Step1Chunk6_0_checked, root7Node95Step1Chunk6_1_checked, root7Node95Step1Chunk6_2_checked, root7Node95Step1Chunk6_3_checked, root7Node95Step1Chunk6_4_checked, root7Node95Step1Chunk6_5_checked, root7Node95Step1Chunk7_0_checked, root7Node95Step1Chunk7_1_checked, root7Node95Step1Chunk7_2_checked, root7Node95Step1Chunk7_3_checked, root7Node95Step1Chunk7_4_checked, root7Node95Step1Chunk7_5_checked, root7Node95Step1Chunk8_0_checked, root7Node95Step1Chunk8_1_checked, root7Node95Step1Chunk8_2_checked, root7Node95Step1Chunk8_3_checked, root7Node95Step1Chunk8_4_checked, root7Node95Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
