module

public import SpectreFinite.RadiusFourRoot5Part4
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable0
public import SpectreFinite.RadiusFourTable11
public import SpectreFinite.RadiusFourTable21
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root5Node14Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(6,5)]
  | 1 => [(0,4),(1,1),(6,1)]
  | 2 => [(5,1),(5,4),(8,1)]
  | 3 => [(0,0),(0,1),(6,4),(6,5)]
  | 4 => [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => [(5,2),(5,5),(8,5)]
  | 6 => [(7,0),(8,0)]
  | 7 => [(4,3),(8,3)]
  | 8 => [(1,5),(3,5),(5,5),(7,5)]
  | 9 => [(0,3),(1,0),(3,0),(6,1)]
  | 10 => [(2,1),(2,5),(4,1),(4,5)]
  | 11 => [(0,5),(6,2),(6,3)]
  | 12 => [(4,4),(7,2),(8,4)]
  | 13 => [(1,4),(7,4)]
  | 14 => [(0,5),(6,3)]
  | 15 => [(2,0),(2,2),(2,4),(4,4)]
  | 16 => [(0,0),(1,3),(3,3),(7,3)]
  | 17 => [(3,2),(5,2),(7,2)]
  | 18 => [(0,2),(1,0),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(0,2),(6,0)]
  | 22 => [(1,1),(3,1),(7,1)]
  | 23 => [(0,1),(1,5),(6,5)]
  | 24 => [(0,4),(6,1),(6,2)]
  | 25 => [(5,1),(5,4),(8,1),(8,4)]
  | 26 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0),(8,0)]
  | 28 => [(7,3)]
  | 29 => [(5,2),(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(1,0),(7,0)]
  | 33 => [(4,3),(7,1),(8,3)]
  | 34 => [(7,5),(8,5)]
  | 35 => [(5,1),(5,4),(8,1),(8,4)]
  | 36 => [(0,1),(6,4)]
  | 37 => [(1,2),(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0),(7,4)]
  | 42 => [(1,3),(6,3),(7,3)]
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
def root5Node14Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(6,4),(6,5)]
  | 4 => some [(0,4),(1,1),(1,2),(3,1),(6,2),(7,1),(7,2)]
  | 5 => some [(5,2),(5,5),(8,5)]
  | 6 => some [(7,0),(8,0)]
  | 7 => some [(4,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,5),(7,5)]
  | 9 => some [(0,3),(1,0),(3,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1),(4,5)]
  | 11 => some [(0,5),(6,2),(6,3)]
  | 12 => some [(4,4),(7,2),(8,4)]
  | 13 => some [(1,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(0,2),(1,0),(6,0)]
  | 19 => some [(1,1),(7,1)]
  | 20 => some [(4,1),(7,5)]
  | 21 => some [(0,2),(6,0)]
  | 22 => some [(1,1),(3,1),(7,1)]
  | 23 => some [(0,1),(1,5),(6,5)]
  | 24 => some [(0,4),(6,1),(6,2)]
  | 25 => some [(5,1),(5,4),(8,1),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0),(8,0)]
  | 28 => some [(7,3)]
  | 29 => some [(5,2),(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(1,0),(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
  | 35 => some [(5,1),(5,4),(8,1),(8,4)]
  | 36 => some [(0,1),(6,4)]
  | 37 => some [(1,2),(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(6,3),(7,3)]
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
theorem root5Node14Domains2_fast_eq : root5Node14Domains2 = expandDomains root5Node14Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node14Domains2 v = expandDomains root5Node14Domains2Fast v from by decide) v
theorem root5Node14Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root5Node14Domains1 root5Node14Domains2 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains1 root5Node14Domains2
    root5Node14Domains1Fast root5Node14Domains2Fast
    root5Node14Domains1_fast_eq root5Node14Domains2_fast_eq (by decide)
theorem root5Node14Step2_checked :
    checkReplacement table46 root5Node14Domains1 root5Node14Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node14Step2Chunk0_0_checked, root5Node14Step2Chunk0_1_checked, root5Node14Step2Chunk0_2_checked, root5Node14Step2Chunk0_3_checked, root5Node14Step2Chunk0_4_checked, root5Node14Step2Chunk0_5_checked, root5Node14Step2Chunk1_0_checked, root5Node14Step2Chunk1_1_checked, root5Node14Step2Chunk1_2_checked, root5Node14Step2Chunk1_3_checked, root5Node14Step2Chunk1_4_checked, root5Node14Step2Chunk1_5_checked, root5Node14Step2Chunk2_0_checked, root5Node14Step2Chunk2_1_checked, root5Node14Step2Chunk2_2_checked, root5Node14Step2Chunk2_3_checked, root5Node14Step2Chunk2_4_checked, root5Node14Step2Chunk2_5_checked, root5Node14Step2Chunk3_0_checked, root5Node14Step2Chunk3_1_checked, root5Node14Step2Chunk3_2_checked, root5Node14Step2Chunk3_3_checked, root5Node14Step2Chunk3_4_checked, root5Node14Step2Chunk3_5_checked, root5Node14Step2Chunk4_0_checked, root5Node14Step2Chunk4_1_checked, root5Node14Step2Chunk4_2_checked, root5Node14Step2Chunk4_3_checked, root5Node14Step2Chunk4_4_checked, root5Node14Step2Chunk4_5_checked, root5Node14Step2Chunk5_0_checked, root5Node14Step2Chunk5_1_checked, root5Node14Step2Chunk5_2_checked, root5Node14Step2Chunk5_3_checked, root5Node14Step2Chunk5_4_checked, root5Node14Step2Chunk5_5_checked, root5Node14Step2Chunk6_0_checked, root5Node14Step2Chunk6_1_checked, root5Node14Step2Chunk6_2_checked, root5Node14Step2Chunk6_3_checked, root5Node14Step2Chunk6_4_checked, root5Node14Step2Chunk6_5_checked, root5Node14Step2Chunk7_0_checked, root5Node14Step2Chunk7_1_checked, root5Node14Step2Chunk7_2_checked, root5Node14Step2Chunk7_3_checked, root5Node14Step2Chunk7_4_checked, root5Node14Step2Chunk7_5_checked, root5Node14Step2Chunk8_0_checked, root5Node14Step2Chunk8_1_checked, root5Node14Step2Chunk8_2_checked, root5Node14Step2Chunk8_3_checked, root5Node14Step2Chunk8_4_checked, root5Node14Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node14Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(6,5)]
  | 1 => [(0,4),(1,1),(6,1)]
  | 2 => [(5,1),(5,4),(8,1)]
  | 3 => [(0,0),(0,1),(6,4),(6,5)]
  | 4 => [(0,4),(1,2),(6,2),(7,2)]
  | 5 => [(5,2),(5,5),(8,5)]
  | 6 => [(7,0),(8,0)]
  | 7 => [(4,3),(8,3)]
  | 8 => [(1,5),(3,5),(5,5),(7,5)]
  | 9 => [(0,3),(1,0),(3,0),(6,1)]
  | 10 => [(2,1),(2,5),(4,1)]
  | 11 => [(0,5),(6,2),(6,3)]
  | 12 => [(4,4),(7,2),(8,4)]
  | 13 => [(1,4),(7,4)]
  | 14 => [(0,5),(6,3)]
  | 15 => [(2,0),(2,2),(2,4),(4,4)]
  | 16 => [(0,0),(1,3),(3,3),(7,3)]
  | 17 => [(3,2),(5,2),(7,2)]
  | 18 => [(0,2),(1,0),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(0,2),(6,0)]
  | 22 => [(1,1),(3,1),(7,1)]
  | 23 => [(0,1),(1,5),(6,5)]
  | 24 => [(0,4),(6,1),(6,2)]
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
  | 35 => [(5,1),(5,4),(8,1),(8,4)]
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
def root5Node14Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(6,4),(6,5)]
  | 4 => some [(0,4),(1,2),(6,2),(7,2)]
  | 5 => some [(5,2),(5,5),(8,5)]
  | 6 => some [(7,0),(8,0)]
  | 7 => some [(4,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,5),(7,5)]
  | 9 => some [(0,3),(1,0),(3,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1)]
  | 11 => some [(0,5),(6,2),(6,3)]
  | 12 => some [(4,4),(7,2),(8,4)]
  | 13 => some [(1,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(0,2),(1,0),(6,0)]
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
  | 35 => some [(5,1),(5,4),(8,1),(8,4)]
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
theorem root5Node14Domains3_fast_eq : root5Node14Domains3 = expandDomains root5Node14Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node14Domains3 v = expandDomains root5Node14Domains3Fast v from by decide) v
theorem root5Node14Step3Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root5Node14Domains2 root5Node14Domains3 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains2 root5Node14Domains3
    root5Node14Domains2Fast root5Node14Domains3Fast
    root5Node14Domains2_fast_eq root5Node14Domains3_fast_eq (by decide)
theorem root5Node14Step3_checked :
    checkReplacement table23 root5Node14Domains2 root5Node14Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node14Step3Chunk0_0_checked, root5Node14Step3Chunk0_1_checked, root5Node14Step3Chunk0_2_checked, root5Node14Step3Chunk0_3_checked, root5Node14Step3Chunk0_4_checked, root5Node14Step3Chunk0_5_checked, root5Node14Step3Chunk1_0_checked, root5Node14Step3Chunk1_1_checked, root5Node14Step3Chunk1_2_checked, root5Node14Step3Chunk1_3_checked, root5Node14Step3Chunk1_4_checked, root5Node14Step3Chunk1_5_checked, root5Node14Step3Chunk2_0_checked, root5Node14Step3Chunk2_1_checked, root5Node14Step3Chunk2_2_checked, root5Node14Step3Chunk2_3_checked, root5Node14Step3Chunk2_4_checked, root5Node14Step3Chunk2_5_checked, root5Node14Step3Chunk3_0_checked, root5Node14Step3Chunk3_1_checked, root5Node14Step3Chunk3_2_checked, root5Node14Step3Chunk3_3_checked, root5Node14Step3Chunk3_4_checked, root5Node14Step3Chunk3_5_checked, root5Node14Step3Chunk4_0_checked, root5Node14Step3Chunk4_1_checked, root5Node14Step3Chunk4_2_checked, root5Node14Step3Chunk4_3_checked, root5Node14Step3Chunk4_4_checked, root5Node14Step3Chunk4_5_checked, root5Node14Step3Chunk5_0_checked, root5Node14Step3Chunk5_1_checked, root5Node14Step3Chunk5_2_checked, root5Node14Step3Chunk5_3_checked, root5Node14Step3Chunk5_4_checked, root5Node14Step3Chunk5_5_checked, root5Node14Step3Chunk6_0_checked, root5Node14Step3Chunk6_1_checked, root5Node14Step3Chunk6_2_checked, root5Node14Step3Chunk6_3_checked, root5Node14Step3Chunk6_4_checked, root5Node14Step3Chunk6_5_checked, root5Node14Step3Chunk7_0_checked, root5Node14Step3Chunk7_1_checked, root5Node14Step3Chunk7_2_checked, root5Node14Step3Chunk7_3_checked, root5Node14Step3Chunk7_4_checked, root5Node14Step3Chunk7_5_checked, root5Node14Step3Chunk8_0_checked, root5Node14Step3Chunk8_1_checked, root5Node14Step3Chunk8_2_checked, root5Node14Step3Chunk8_3_checked, root5Node14Step3Chunk8_4_checked, root5Node14Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node14Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2),(1,5),(6,5)]
  | 1 => [(0,4),(1,1),(6,1)]
  | 2 => [(5,1),(5,4),(8,1)]
  | 3 => [(0,0),(0,1),(6,4),(6,5)]
  | 4 => [(0,4),(1,2),(6,2),(7,2)]
  | 5 => [(5,2),(5,5),(8,5)]
  | 6 => [(7,0),(8,0)]
  | 7 => [(4,3),(8,3)]
  | 8 => [(1,5),(3,5),(5,5),(7,5)]
  | 9 => [(0,3),(1,0),(3,0),(6,1)]
  | 10 => [(2,1),(2,5),(4,1)]
  | 11 => [(0,5),(6,2),(6,3)]
  | 12 => [(4,4),(7,2),(8,4)]
  | 13 => [(1,4),(7,4)]
  | 14 => [(0,5),(6,3)]
  | 15 => [(2,0),(2,2),(2,4),(4,4)]
  | 16 => [(0,0),(1,3),(3,3),(7,3)]
  | 17 => [(3,2),(5,2),(7,2)]
  | 18 => [(0,2),(1,0),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(0,2),(6,0)]
  | 22 => [(1,1),(3,1),(7,1)]
  | 23 => [(0,1),(1,5),(6,5)]
  | 24 => [(0,4),(6,1),(6,2)]
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
def root5Node14Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(6,4),(6,5)]
  | 4 => some [(0,4),(1,2),(6,2),(7,2)]
  | 5 => some [(5,2),(5,5),(8,5)]
  | 6 => some [(7,0),(8,0)]
  | 7 => some [(4,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,5),(7,5)]
  | 9 => some [(0,3),(1,0),(3,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1)]
  | 11 => some [(0,5),(6,2),(6,3)]
  | 12 => some [(4,4),(7,2),(8,4)]
  | 13 => some [(1,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(0,2),(1,0),(6,0)]
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
theorem root5Node14Domains4_fast_eq : root5Node14Domains4 = expandDomains root5Node14Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node14Domains4 v = expandDomains root5Node14Domains4Fast v from by decide) v
theorem root5Node14Step4Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root5Node14Domains3 root5Node14Domains4 = true := by
  exact checkNarrowing_of_fast _ root5Node14Domains3 root5Node14Domains4
    root5Node14Domains3Fast root5Node14Domains4Fast
    root5Node14Domains3_fast_eq root5Node14Domains4_fast_eq (by decide)
theorem root5Node14Step4_checked :
    checkReplacement table11 root5Node14Domains3 root5Node14Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node14Step4Chunk0_0_checked, root5Node14Step4Chunk0_1_checked, root5Node14Step4Chunk0_2_checked, root5Node14Step4Chunk0_3_checked, root5Node14Step4Chunk0_4_checked, root5Node14Step4Chunk0_5_checked, root5Node14Step4Chunk1_0_checked, root5Node14Step4Chunk1_1_checked, root5Node14Step4Chunk1_2_checked, root5Node14Step4Chunk1_3_checked, root5Node14Step4Chunk1_4_checked, root5Node14Step4Chunk1_5_checked, root5Node14Step4Chunk2_0_checked, root5Node14Step4Chunk2_1_checked, root5Node14Step4Chunk2_2_checked, root5Node14Step4Chunk2_3_checked, root5Node14Step4Chunk2_4_checked, root5Node14Step4Chunk2_5_checked, root5Node14Step4Chunk3_0_checked, root5Node14Step4Chunk3_1_checked, root5Node14Step4Chunk3_2_checked, root5Node14Step4Chunk3_3_checked, root5Node14Step4Chunk3_4_checked, root5Node14Step4Chunk3_5_checked, root5Node14Step4Chunk4_0_checked, root5Node14Step4Chunk4_1_checked, root5Node14Step4Chunk4_2_checked, root5Node14Step4Chunk4_3_checked, root5Node14Step4Chunk4_4_checked, root5Node14Step4Chunk4_5_checked, root5Node14Step4Chunk5_0_checked, root5Node14Step4Chunk5_1_checked, root5Node14Step4Chunk5_2_checked, root5Node14Step4Chunk5_3_checked, root5Node14Step4Chunk5_4_checked, root5Node14Step4Chunk5_5_checked, root5Node14Step4Chunk6_0_checked, root5Node14Step4Chunk6_1_checked, root5Node14Step4Chunk6_2_checked, root5Node14Step4Chunk6_3_checked, root5Node14Step4Chunk6_4_checked, root5Node14Step4Chunk6_5_checked, root5Node14Step4Chunk7_0_checked, root5Node14Step4Chunk7_1_checked, root5Node14Step4Chunk7_2_checked, root5Node14Step4Chunk7_3_checked, root5Node14Step4Chunk7_4_checked, root5Node14Step4Chunk7_5_checked, root5Node14Step4Chunk8_0_checked, root5Node14Step4Chunk8_1_checked, root5Node14Step4Chunk8_2_checked, root5Node14Step4Chunk8_3_checked, root5Node14Step4Chunk8_4_checked, root5Node14Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node15Domains0 : Domains 61 State := restrict root5Node14Domains4 6 (7,0)
def root5Node15Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,5),(6,5)]
  | 1 => some [(0,4),(1,1),(6,1)]
  | 2 => some [(5,1),(5,4),(8,1)]
  | 3 => some [(0,0),(0,1),(6,4),(6,5)]
  | 4 => some [(0,4),(1,2),(6,2),(7,2)]
  | 5 => some [(5,2),(5,5),(8,5)]
  | 6 => some [(7,0)]
  | 7 => some [(4,3),(8,3)]
  | 8 => some [(1,5),(3,5),(5,5),(7,5)]
  | 9 => some [(0,3),(1,0),(3,0),(6,1)]
  | 10 => some [(2,1),(2,5),(4,1)]
  | 11 => some [(0,5),(6,2),(6,3)]
  | 12 => some [(4,4),(7,2),(8,4)]
  | 13 => some [(1,4),(7,4)]
  | 14 => some [(0,5),(6,3)]
  | 15 => some [(2,0),(2,2),(2,4),(4,4)]
  | 16 => some [(0,0),(1,3),(3,3),(7,3)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(0,2),(1,0),(6,0)]
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
theorem root5Node15Domains0_fast_eq : root5Node15Domains0 = expandDomains root5Node15Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node15Domains0 v = expandDomains root5Node15Domains0Fast v from by decide) v
def root5Node15Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5),(6,5)]
  | 1 => [(0,4),(6,1)]
  | 2 => [(5,1),(5,4),(8,1)]
  | 3 => [(0,0),(0,1),(6,4),(6,5)]
  | 4 => [(0,4),(1,2),(6,2),(7,2)]
  | 5 => [(5,5),(8,5)]
  | 6 => [(7,0)]
  | 7 => [(4,3),(8,3)]
  | 8 => [(1,5),(3,5),(5,5),(7,5)]
  | 9 => [(0,3),(1,0),(3,0),(6,1)]
  | 10 => [(2,1),(2,5),(4,1)]
  | 11 => [(0,5),(6,3)]
  | 12 => [(4,4),(7,2)]
  | 13 => [(1,4),(7,4)]
  | 14 => [(0,5),(6,3)]
  | 15 => [(2,0),(2,2),(2,4),(4,4)]
  | 16 => [(0,0),(1,3),(3,3),(7,3)]
  | 17 => [(3,2),(5,2),(7,2)]
  | 18 => [(0,2),(6,0)]
  | 19 => [(1,1),(7,1)]
  | 20 => [(4,1),(7,5)]
  | 21 => [(0,2),(6,0)]
  | 22 => [(1,1),(3,1),(7,1)]
  | 23 => [(0,1),(1,5),(6,5)]
  | 24 => [(0,4),(6,1),(6,2)]
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
def root5Node15Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5),(6,5)]
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
theorem root5Node15Domains1_fast_eq : root5Node15Domains1 = expandDomains root5Node15Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node15Domains1 v = expandDomains root5Node15Domains1Fast v from by decide) v
theorem root5Node15Step1Chunk0_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk0_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows0_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk1_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows1_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk2_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows2_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk3_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows3_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk4_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows4_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk5_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows5_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk6_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows6_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk7_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows7_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_0_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_0⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_1_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_1⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_2_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_2⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_3_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_3⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_4_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_4⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1Chunk8_5_checked :
    checkNarrowing ⟨table0Scope, table0Rows8_5⟩
      root5Node15Domains0 root5Node15Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node15Domains0 root5Node15Domains1
    root5Node15Domains0Fast root5Node15Domains1Fast
    root5Node15Domains0_fast_eq root5Node15Domains1_fast_eq (by decide)
theorem root5Node15Step1_checked :
    checkReplacement table0 root5Node15Domains0 root5Node15Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node15Step1Chunk0_0_checked, root5Node15Step1Chunk0_1_checked, root5Node15Step1Chunk0_2_checked, root5Node15Step1Chunk0_3_checked, root5Node15Step1Chunk0_4_checked, root5Node15Step1Chunk0_5_checked, root5Node15Step1Chunk1_0_checked, root5Node15Step1Chunk1_1_checked, root5Node15Step1Chunk1_2_checked, root5Node15Step1Chunk1_3_checked, root5Node15Step1Chunk1_4_checked, root5Node15Step1Chunk1_5_checked, root5Node15Step1Chunk2_0_checked, root5Node15Step1Chunk2_1_checked, root5Node15Step1Chunk2_2_checked, root5Node15Step1Chunk2_3_checked, root5Node15Step1Chunk2_4_checked, root5Node15Step1Chunk2_5_checked, root5Node15Step1Chunk3_0_checked, root5Node15Step1Chunk3_1_checked, root5Node15Step1Chunk3_2_checked, root5Node15Step1Chunk3_3_checked, root5Node15Step1Chunk3_4_checked, root5Node15Step1Chunk3_5_checked, root5Node15Step1Chunk4_0_checked, root5Node15Step1Chunk4_1_checked, root5Node15Step1Chunk4_2_checked, root5Node15Step1Chunk4_3_checked, root5Node15Step1Chunk4_4_checked, root5Node15Step1Chunk4_5_checked, root5Node15Step1Chunk5_0_checked, root5Node15Step1Chunk5_1_checked, root5Node15Step1Chunk5_2_checked, root5Node15Step1Chunk5_3_checked, root5Node15Step1Chunk5_4_checked, root5Node15Step1Chunk5_5_checked, root5Node15Step1Chunk6_0_checked, root5Node15Step1Chunk6_1_checked, root5Node15Step1Chunk6_2_checked, root5Node15Step1Chunk6_3_checked, root5Node15Step1Chunk6_4_checked, root5Node15Step1Chunk6_5_checked, root5Node15Step1Chunk7_0_checked, root5Node15Step1Chunk7_1_checked, root5Node15Step1Chunk7_2_checked, root5Node15Step1Chunk7_3_checked, root5Node15Step1Chunk7_4_checked, root5Node15Step1Chunk7_5_checked, root5Node15Step1Chunk8_0_checked, root5Node15Step1Chunk8_1_checked, root5Node15Step1Chunk8_2_checked, root5Node15Step1Chunk8_3_checked, root5Node15Step1Chunk8_4_checked, root5Node15Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root5Node16Domains0 : Domains 61 State := restrict root5Node15Domains1 0 (1,5)
def root5Node16Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
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
theorem root5Node16Domains0_fast_eq : root5Node16Domains0 = expandDomains root5Node16Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node16Domains0 v = expandDomains root5Node16Domains0Fast v from by decide) v
def root5Node16Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5)]
  | 1 => [(6,1)]
  | 2 => [(5,1),(8,1)]
  | 3 => [(0,1),(6,5)]
  | 4 => [(0,4),(1,2),(6,2),(7,2)]
  | 5 => [(5,5)]
  | 6 => [(7,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(1,0),(3,0)]
  | 10 => [(2,1),(2,5),(4,1)]
  | 11 => [(0,5)]
  | 12 => [(4,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(0,0)]
  | 17 => [(3,2),(5,2),(7,2)]
  | 18 => [(6,0)]
  | 19 => [(7,1)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(1,5)]
  | 24 => [(6,1)]
  | 25 => [(5,1),(5,4),(8,4)]
  | 26 => [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => [(4,0)]
  | 28 => [(7,3)]
  | 29 => [(8,2)]
  | 30 => [(5,0)]
  | 31 => [(4,5)]
  | 32 => [(7,0)]
  | 33 => [(4,3),(7,1),(8,3)]
  | 34 => [(7,5),(8,5)]
  | 35 => [(5,1),(5,4),(8,4)]
  | 36 => [(0,1)]
  | 37 => [(6,2)]
  | 38 => [(8,4)]
  | 39 => [(0,0)]
  | 40 => [(7,2)]
  | 41 => [(4,0),(7,4)]
  | 42 => [(1,3),(7,3)]
  | 43 => [(7,5),(8,5)]
  | 44 => [(1,0)]
  | 45 => [(7,1)]
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
def root5Node16Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5)]
  | 1 => some [(6,1)]
  | 2 => some [(5,1),(8,1)]
  | 3 => some [(0,1),(6,5)]
  | 4 => some [(0,4),(1,2),(6,2),(7,2)]
  | 5 => some [(5,5)]
  | 6 => some [(7,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(1,0),(3,0)]
  | 10 => some [(2,1),(2,5),(4,1)]
  | 11 => some [(0,5)]
  | 12 => some [(4,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(0,0)]
  | 17 => some [(3,2),(5,2),(7,2)]
  | 18 => some [(6,0)]
  | 19 => some [(7,1)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(1,5)]
  | 24 => some [(6,1)]
  | 25 => some [(5,1),(5,4),(8,4)]
  | 26 => some [(1,2),(3,2),(5,2),(7,2),(8,2)]
  | 27 => some [(4,0)]
  | 28 => some [(7,3)]
  | 29 => some [(8,2)]
  | 30 => some [(5,0)]
  | 31 => some [(4,5)]
  | 32 => some [(7,0)]
  | 33 => some [(4,3),(7,1),(8,3)]
  | 34 => some [(7,5),(8,5)]
  | 35 => some [(5,1),(5,4),(8,4)]
  | 36 => some [(0,1)]
  | 37 => some [(6,2)]
  | 38 => some [(8,4)]
  | 39 => some [(0,0)]
  | 40 => some [(7,2)]
  | 41 => some [(4,0),(7,4)]
  | 42 => some [(1,3),(7,3)]
  | 43 => some [(7,5),(8,5)]
  | 44 => some [(1,0)]
  | 45 => some [(7,1)]
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
theorem root5Node16Domains1_fast_eq : root5Node16Domains1 = expandDomains root5Node16Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root5Node16Domains1 v = expandDomains root5Node16Domains1Fast v from by decide) v
theorem root5Node16Step1Chunk0_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk0_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows0_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk1_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows1_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk2_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows2_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk3_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows3_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk4_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows4_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk5_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows5_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk6_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows6_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk7_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows7_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_0_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_0⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_1_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_1⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_2_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_2⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_3_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_3⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_4_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_4⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1Chunk8_5_checked :
    checkNarrowing ⟨table21Scope, table21Rows8_5⟩
      root5Node16Domains0 root5Node16Domains1 = true := by
  exact checkNarrowing_of_fast _ root5Node16Domains0 root5Node16Domains1
    root5Node16Domains0Fast root5Node16Domains1Fast
    root5Node16Domains0_fast_eq root5Node16Domains1_fast_eq (by decide)
theorem root5Node16Step1_checked :
    checkReplacement table21 root5Node16Domains0 root5Node16Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root5Node16Step1Chunk0_0_checked, root5Node16Step1Chunk0_1_checked, root5Node16Step1Chunk0_2_checked, root5Node16Step1Chunk0_3_checked, root5Node16Step1Chunk0_4_checked, root5Node16Step1Chunk0_5_checked, root5Node16Step1Chunk1_0_checked, root5Node16Step1Chunk1_1_checked, root5Node16Step1Chunk1_2_checked, root5Node16Step1Chunk1_3_checked, root5Node16Step1Chunk1_4_checked, root5Node16Step1Chunk1_5_checked, root5Node16Step1Chunk2_0_checked, root5Node16Step1Chunk2_1_checked, root5Node16Step1Chunk2_2_checked, root5Node16Step1Chunk2_3_checked, root5Node16Step1Chunk2_4_checked, root5Node16Step1Chunk2_5_checked, root5Node16Step1Chunk3_0_checked, root5Node16Step1Chunk3_1_checked, root5Node16Step1Chunk3_2_checked, root5Node16Step1Chunk3_3_checked, root5Node16Step1Chunk3_4_checked, root5Node16Step1Chunk3_5_checked, root5Node16Step1Chunk4_0_checked, root5Node16Step1Chunk4_1_checked, root5Node16Step1Chunk4_2_checked, root5Node16Step1Chunk4_3_checked, root5Node16Step1Chunk4_4_checked, root5Node16Step1Chunk4_5_checked, root5Node16Step1Chunk5_0_checked, root5Node16Step1Chunk5_1_checked, root5Node16Step1Chunk5_2_checked, root5Node16Step1Chunk5_3_checked, root5Node16Step1Chunk5_4_checked, root5Node16Step1Chunk5_5_checked, root5Node16Step1Chunk6_0_checked, root5Node16Step1Chunk6_1_checked, root5Node16Step1Chunk6_2_checked, root5Node16Step1Chunk6_3_checked, root5Node16Step1Chunk6_4_checked, root5Node16Step1Chunk6_5_checked, root5Node16Step1Chunk7_0_checked, root5Node16Step1Chunk7_1_checked, root5Node16Step1Chunk7_2_checked, root5Node16Step1Chunk7_3_checked, root5Node16Step1Chunk7_4_checked, root5Node16Step1Chunk7_5_checked, root5Node16Step1Chunk8_0_checked, root5Node16Step1Chunk8_1_checked, root5Node16Step1Chunk8_2_checked, root5Node16Step1Chunk8_3_checked, root5Node16Step1Chunk8_4_checked, root5Node16Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
