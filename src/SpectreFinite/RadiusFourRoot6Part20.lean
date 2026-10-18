module

public import SpectreFinite.RadiusFourRoot6Part19
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable11
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node72Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(4,5),(7,3)]
  | 5 => [(8,1)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(5,1),(8,1)]
  | 9 => [(0,1),(6,5)]
  | 10 => [(0,4),(1,2),(6,2),(7,2)]
  | 11 => [(5,3)]
  | 12 => [(5,5)]
  | 13 => [(7,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0),(3,0),(7,0)]
  | 17 => [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 18 => [(1,4)]
  | 19 => [(0,5)]
  | 20 => [(4,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 26 => [(2,5),(4,5),(7,5),(8,5)]
  | 27 => [(6,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 34 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0),(6,4)]
  | 48 => [(1,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(8,1)]
  | 56 => [(7,2),(8,2)]
  | 57 => [(4,0),(5,0),(8,0)]
  | 58 => [(4,5),(7,3)]
  | 59 => [(4,2),(7,0)]
  | _ => [(5,3),(8,3)]
def root6Node72Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(4,5),(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(5,1),(8,1)]
  | 9 => some [(0,1),(6,5)]
  | 10 => some [(0,4),(1,2),(6,2),(7,2)]
  | 11 => some [(5,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,1),(4,3)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 26 => some [(2,5),(4,5),(7,5),(8,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(0,4),(6,0),(6,1),(6,2)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(4,3),(5,0),(5,3),(7,1),(8,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2),(8,2)]
  | 57 => some [(4,0),(5,0),(8,0)]
  | 58 => some [(4,5),(7,3)]
  | 59 => some [(4,2),(7,0)]
  | _ => some [(5,3),(8,3)]
theorem root6Node72Domains2_fast_eq : root6Node72Domains2 = expandDomains root6Node72Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node72Domains2 v = expandDomains root6Node72Domains2Fast v from by decide) v
theorem root6Node72Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root6Node72Domains1 root6Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains1 root6Node72Domains2
    root6Node72Domains1Fast root6Node72Domains2Fast
    root6Node72Domains1_fast_eq root6Node72Domains2_fast_eq (by decide)
theorem root6Node72Step2_checked :
    checkReplacement table46 root6Node72Domains1 root6Node72Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node72Step2Chunk0_0_checked, root6Node72Step2Chunk0_1_checked, root6Node72Step2Chunk0_2_checked, root6Node72Step2Chunk0_3_checked, root6Node72Step2Chunk0_4_checked, root6Node72Step2Chunk0_5_checked, root6Node72Step2Chunk1_0_checked, root6Node72Step2Chunk1_1_checked, root6Node72Step2Chunk1_2_checked, root6Node72Step2Chunk1_3_checked, root6Node72Step2Chunk1_4_checked, root6Node72Step2Chunk1_5_checked, root6Node72Step2Chunk2_0_checked, root6Node72Step2Chunk2_1_checked, root6Node72Step2Chunk2_2_checked, root6Node72Step2Chunk2_3_checked, root6Node72Step2Chunk2_4_checked, root6Node72Step2Chunk2_5_checked, root6Node72Step2Chunk3_0_checked, root6Node72Step2Chunk3_1_checked, root6Node72Step2Chunk3_2_checked, root6Node72Step2Chunk3_3_checked, root6Node72Step2Chunk3_4_checked, root6Node72Step2Chunk3_5_checked, root6Node72Step2Chunk4_0_checked, root6Node72Step2Chunk4_1_checked, root6Node72Step2Chunk4_2_checked, root6Node72Step2Chunk4_3_checked, root6Node72Step2Chunk4_4_checked, root6Node72Step2Chunk4_5_checked, root6Node72Step2Chunk5_0_checked, root6Node72Step2Chunk5_1_checked, root6Node72Step2Chunk5_2_checked, root6Node72Step2Chunk5_3_checked, root6Node72Step2Chunk5_4_checked, root6Node72Step2Chunk5_5_checked, root6Node72Step2Chunk6_0_checked, root6Node72Step2Chunk6_1_checked, root6Node72Step2Chunk6_2_checked, root6Node72Step2Chunk6_3_checked, root6Node72Step2Chunk6_4_checked, root6Node72Step2Chunk6_5_checked, root6Node72Step2Chunk7_0_checked, root6Node72Step2Chunk7_1_checked, root6Node72Step2Chunk7_2_checked, root6Node72Step2Chunk7_3_checked, root6Node72Step2Chunk7_4_checked, root6Node72Step2Chunk7_5_checked, root6Node72Step2Chunk8_0_checked, root6Node72Step2Chunk8_1_checked, root6Node72Step2Chunk8_2_checked, root6Node72Step2Chunk8_3_checked, root6Node72Step2Chunk8_4_checked, root6Node72Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node72Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(7,3)]
  | 5 => [(8,1)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(5,1),(8,1)]
  | 9 => [(0,1),(6,5)]
  | 10 => [(0,4),(6,2)]
  | 11 => [(5,3)]
  | 12 => [(5,5)]
  | 13 => [(7,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0),(3,0),(7,0)]
  | 17 => [(2,1),(2,3),(2,5),(4,3)]
  | 18 => [(1,4)]
  | 19 => [(0,5)]
  | 20 => [(4,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(3,2),(7,2)]
  | 26 => [(2,5),(4,5),(7,5),(8,5)]
  | 27 => [(6,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(3,1),(5,1),(7,1)]
  | 35 => [(7,2),(8,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0),(6,4)]
  | 48 => [(1,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(8,1)]
  | 56 => [(7,2),(8,2)]
  | 57 => [(4,0),(5,0),(8,0)]
  | 58 => [(4,5),(7,3)]
  | 59 => [(4,2),(7,0)]
  | _ => [(5,3),(8,3)]
def root6Node72Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(5,1),(8,1)]
  | 9 => some [(0,1),(6,5)]
  | 10 => some [(0,4),(6,2)]
  | 11 => some [(5,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,3)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(3,2),(7,2)]
  | 26 => some [(2,5),(4,5),(7,5),(8,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(3,1),(5,1),(7,1)]
  | 35 => some [(7,2),(8,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2),(8,2)]
  | 57 => some [(4,0),(5,0),(8,0)]
  | 58 => some [(4,5),(7,3)]
  | 59 => some [(4,2),(7,0)]
  | _ => some [(5,3),(8,3)]
theorem root6Node72Domains3_fast_eq : root6Node72Domains3 = expandDomains root6Node72Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node72Domains3 v = expandDomains root6Node72Domains3Fast v from by decide) v
theorem root6Node72Step3Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root6Node72Domains2 root6Node72Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains2 root6Node72Domains3
    root6Node72Domains2Fast root6Node72Domains3Fast
    root6Node72Domains2_fast_eq root6Node72Domains3_fast_eq (by decide)
theorem root6Node72Step3_checked :
    checkReplacement table16 root6Node72Domains2 root6Node72Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node72Step3Chunk0_0_checked, root6Node72Step3Chunk0_1_checked, root6Node72Step3Chunk0_2_checked, root6Node72Step3Chunk0_3_checked, root6Node72Step3Chunk0_4_checked, root6Node72Step3Chunk0_5_checked, root6Node72Step3Chunk1_0_checked, root6Node72Step3Chunk1_1_checked, root6Node72Step3Chunk1_2_checked, root6Node72Step3Chunk1_3_checked, root6Node72Step3Chunk1_4_checked, root6Node72Step3Chunk1_5_checked, root6Node72Step3Chunk2_0_checked, root6Node72Step3Chunk2_1_checked, root6Node72Step3Chunk2_2_checked, root6Node72Step3Chunk2_3_checked, root6Node72Step3Chunk2_4_checked, root6Node72Step3Chunk2_5_checked, root6Node72Step3Chunk3_0_checked, root6Node72Step3Chunk3_1_checked, root6Node72Step3Chunk3_2_checked, root6Node72Step3Chunk3_3_checked, root6Node72Step3Chunk3_4_checked, root6Node72Step3Chunk3_5_checked, root6Node72Step3Chunk4_0_checked, root6Node72Step3Chunk4_1_checked, root6Node72Step3Chunk4_2_checked, root6Node72Step3Chunk4_3_checked, root6Node72Step3Chunk4_4_checked, root6Node72Step3Chunk4_5_checked, root6Node72Step3Chunk5_0_checked, root6Node72Step3Chunk5_1_checked, root6Node72Step3Chunk5_2_checked, root6Node72Step3Chunk5_3_checked, root6Node72Step3Chunk5_4_checked, root6Node72Step3Chunk5_5_checked, root6Node72Step3Chunk6_0_checked, root6Node72Step3Chunk6_1_checked, root6Node72Step3Chunk6_2_checked, root6Node72Step3Chunk6_3_checked, root6Node72Step3Chunk6_4_checked, root6Node72Step3Chunk6_5_checked, root6Node72Step3Chunk7_0_checked, root6Node72Step3Chunk7_1_checked, root6Node72Step3Chunk7_2_checked, root6Node72Step3Chunk7_3_checked, root6Node72Step3Chunk7_4_checked, root6Node72Step3Chunk7_5_checked, root6Node72Step3Chunk8_0_checked, root6Node72Step3Chunk8_1_checked, root6Node72Step3Chunk8_2_checked, root6Node72Step3Chunk8_3_checked, root6Node72Step3Chunk8_4_checked, root6Node72Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node72Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0),(7,4)]
  | 4 => [(1,3),(7,3)]
  | 5 => [(8,1)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(5,1),(8,1)]
  | 9 => [(0,1),(6,5)]
  | 10 => [(0,4),(6,2)]
  | 11 => [(5,3)]
  | 12 => [(5,5)]
  | 13 => [(7,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0),(3,0),(7,0)]
  | 17 => [(2,1),(2,3),(2,5),(4,3)]
  | 18 => [(1,4)]
  | 19 => [(0,5)]
  | 20 => [(4,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0),(1,4),(6,4)]
  | 25 => [(0,5),(1,2),(3,2),(7,2)]
  | 26 => [(2,5)]
  | 27 => [(6,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,0),(6,1)]
  | 34 => [(3,1),(5,1),(7,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0),(8,2)]
  | 42 => [(5,0),(5,3),(8,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0),(6,4)]
  | 48 => [(1,2),(7,2)]
  | 49 => [(7,4),(8,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(8,1)]
  | 56 => [(7,2),(8,2)]
  | 57 => [(4,0),(5,0),(8,0)]
  | 58 => [(4,5),(7,3)]
  | 59 => [(4,2),(7,0)]
  | _ => [(5,3),(8,3)]
def root6Node72Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0),(7,4)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(5,1),(8,1)]
  | 9 => some [(0,1),(6,5)]
  | 10 => some [(0,4),(6,2)]
  | 11 => some [(5,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,3)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(3,2),(7,2)]
  | 26 => some [(2,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(3,1),(5,1),(7,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2),(8,2)]
  | 57 => some [(4,0),(5,0),(8,0)]
  | 58 => some [(4,5),(7,3)]
  | 59 => some [(4,2),(7,0)]
  | _ => some [(5,3),(8,3)]
theorem root6Node72Domains4_fast_eq : root6Node72Domains4 = expandDomains root6Node72Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node72Domains4 v = expandDomains root6Node72Domains4Fast v from by decide) v
theorem root6Node72Step4Chunk0_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_0⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk0_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_1⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk0_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_2⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk0_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_3⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk0_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_4⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk0_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows0_5⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk1_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_0⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk1_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_1⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk1_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_2⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk1_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_3⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk1_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_4⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk1_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows1_5⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk2_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_0⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk2_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_1⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk2_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_2⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk2_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_3⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk2_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_4⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk2_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows2_5⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk3_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_0⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk3_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_1⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk3_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_2⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk3_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_3⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk3_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_4⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk3_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows3_5⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk4_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_0⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk4_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_1⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk4_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_2⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk4_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_3⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk4_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_4⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk4_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows4_5⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk5_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_0⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk5_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_1⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk5_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_2⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk5_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_3⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk5_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_4⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk5_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows5_5⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk6_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_0⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk6_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_1⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk6_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_2⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk6_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_3⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk6_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_4⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk6_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows6_5⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk7_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_0⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk7_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_1⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk7_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_2⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk7_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_3⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk7_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_4⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk7_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows7_5⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk8_0_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_0⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk8_1_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_1⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk8_2_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_2⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk8_3_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_3⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk8_4_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_4⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4Chunk8_5_checked :
    checkNarrowing ⟨table11Scope, table11Rows8_5⟩
      root6Node72Domains3 root6Node72Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node72Domains3 root6Node72Domains4
    root6Node72Domains3Fast root6Node72Domains4Fast
    root6Node72Domains3_fast_eq root6Node72Domains4_fast_eq (by decide)
theorem root6Node72Step4_checked :
    checkReplacement table11 root6Node72Domains3 root6Node72Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node72Step4Chunk0_0_checked, root6Node72Step4Chunk0_1_checked, root6Node72Step4Chunk0_2_checked, root6Node72Step4Chunk0_3_checked, root6Node72Step4Chunk0_4_checked, root6Node72Step4Chunk0_5_checked, root6Node72Step4Chunk1_0_checked, root6Node72Step4Chunk1_1_checked, root6Node72Step4Chunk1_2_checked, root6Node72Step4Chunk1_3_checked, root6Node72Step4Chunk1_4_checked, root6Node72Step4Chunk1_5_checked, root6Node72Step4Chunk2_0_checked, root6Node72Step4Chunk2_1_checked, root6Node72Step4Chunk2_2_checked, root6Node72Step4Chunk2_3_checked, root6Node72Step4Chunk2_4_checked, root6Node72Step4Chunk2_5_checked, root6Node72Step4Chunk3_0_checked, root6Node72Step4Chunk3_1_checked, root6Node72Step4Chunk3_2_checked, root6Node72Step4Chunk3_3_checked, root6Node72Step4Chunk3_4_checked, root6Node72Step4Chunk3_5_checked, root6Node72Step4Chunk4_0_checked, root6Node72Step4Chunk4_1_checked, root6Node72Step4Chunk4_2_checked, root6Node72Step4Chunk4_3_checked, root6Node72Step4Chunk4_4_checked, root6Node72Step4Chunk4_5_checked, root6Node72Step4Chunk5_0_checked, root6Node72Step4Chunk5_1_checked, root6Node72Step4Chunk5_2_checked, root6Node72Step4Chunk5_3_checked, root6Node72Step4Chunk5_4_checked, root6Node72Step4Chunk5_5_checked, root6Node72Step4Chunk6_0_checked, root6Node72Step4Chunk6_1_checked, root6Node72Step4Chunk6_2_checked, root6Node72Step4Chunk6_3_checked, root6Node72Step4Chunk6_4_checked, root6Node72Step4Chunk6_5_checked, root6Node72Step4Chunk7_0_checked, root6Node72Step4Chunk7_1_checked, root6Node72Step4Chunk7_2_checked, root6Node72Step4Chunk7_3_checked, root6Node72Step4Chunk7_4_checked, root6Node72Step4Chunk7_5_checked, root6Node72Step4Chunk8_0_checked, root6Node72Step4Chunk8_1_checked, root6Node72Step4Chunk8_2_checked, root6Node72Step4Chunk8_3_checked, root6Node72Step4Chunk8_4_checked, root6Node72Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node73Domains0 : Domains 61 State := restrict root6Node72Domains4 3 (4,0)
def root6Node73Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(1,3),(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(5,1),(8,1)]
  | 9 => some [(0,1),(6,5)]
  | 10 => some [(0,4),(6,2)]
  | 11 => some [(5,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0),(3,0),(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,3)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0),(1,4),(6,4)]
  | 25 => some [(0,5),(1,2),(3,2),(7,2)]
  | 26 => some [(2,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,0),(6,1)]
  | 34 => some [(3,1),(5,1),(7,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0),(8,2)]
  | 42 => some [(5,0),(5,3),(8,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0),(6,4)]
  | 48 => some [(1,2),(7,2)]
  | 49 => some [(7,4),(8,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2),(8,2)]
  | 57 => some [(4,0),(5,0),(8,0)]
  | 58 => some [(4,5),(7,3)]
  | 59 => some [(4,2),(7,0)]
  | _ => some [(5,3),(8,3)]
theorem root6Node73Domains0_fast_eq : root6Node73Domains0 = expandDomains root6Node73Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node73Domains0 v = expandDomains root6Node73Domains0Fast v from by decide) v
def root6Node73Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,1)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(5,1)]
  | 9 => [(0,1)]
  | 10 => [(6,2)]
  | 11 => [(5,3)]
  | 12 => [(5,5)]
  | 13 => [(7,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0)]
  | 17 => [(2,1)]
  | 18 => [(1,4)]
  | 19 => [(0,5)]
  | 20 => [(4,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0)]
  | 25 => [(3,2)]
  | 26 => [(2,5)]
  | 27 => [(6,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5),(7,5)]
  | 54 => [(0,3),(6,1)]
  | 55 => [(8,1)]
  | 56 => [(7,2),(8,2)]
  | 57 => [(4,0),(5,0),(8,0)]
  | 58 => [(4,5),(7,3)]
  | 59 => [(4,2),(7,0)]
  | _ => [(5,3),(8,3)]
def root6Node73Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(5,1)]
  | 9 => some [(0,1)]
  | 10 => some [(6,2)]
  | 11 => some [(5,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0)]
  | 17 => some [(2,1)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(3,2)]
  | 26 => some [(2,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5),(7,5)]
  | 54 => some [(0,3),(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(7,2),(8,2)]
  | 57 => some [(4,0),(5,0),(8,0)]
  | 58 => some [(4,5),(7,3)]
  | 59 => some [(4,2),(7,0)]
  | _ => some [(5,3),(8,3)]
theorem root6Node73Domains1_fast_eq : root6Node73Domains1 = expandDomains root6Node73Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node73Domains1 v = expandDomains root6Node73Domains1Fast v from by decide) v
theorem root6Node73Step1Chunk0_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk0_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk0_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk0_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk0_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk0_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows0_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk1_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows1_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk2_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows2_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk3_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows3_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk4_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows4_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk5_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows5_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk6_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows6_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk7_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows7_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_0_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_0⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_1_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_1⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_2_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_2⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_3_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_3⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_4_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_4⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1Chunk8_5_checked :
    checkNarrowing ⟨table23Scope, table23Rows8_5⟩
      root6Node73Domains0 root6Node73Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains0 root6Node73Domains1
    root6Node73Domains0Fast root6Node73Domains1Fast
    root6Node73Domains0_fast_eq root6Node73Domains1_fast_eq (by decide)
theorem root6Node73Step1_checked :
    checkReplacement table23 root6Node73Domains0 root6Node73Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node73Step1Chunk0_0_checked, root6Node73Step1Chunk0_1_checked, root6Node73Step1Chunk0_2_checked, root6Node73Step1Chunk0_3_checked, root6Node73Step1Chunk0_4_checked, root6Node73Step1Chunk0_5_checked, root6Node73Step1Chunk1_0_checked, root6Node73Step1Chunk1_1_checked, root6Node73Step1Chunk1_2_checked, root6Node73Step1Chunk1_3_checked, root6Node73Step1Chunk1_4_checked, root6Node73Step1Chunk1_5_checked, root6Node73Step1Chunk2_0_checked, root6Node73Step1Chunk2_1_checked, root6Node73Step1Chunk2_2_checked, root6Node73Step1Chunk2_3_checked, root6Node73Step1Chunk2_4_checked, root6Node73Step1Chunk2_5_checked, root6Node73Step1Chunk3_0_checked, root6Node73Step1Chunk3_1_checked, root6Node73Step1Chunk3_2_checked, root6Node73Step1Chunk3_3_checked, root6Node73Step1Chunk3_4_checked, root6Node73Step1Chunk3_5_checked, root6Node73Step1Chunk4_0_checked, root6Node73Step1Chunk4_1_checked, root6Node73Step1Chunk4_2_checked, root6Node73Step1Chunk4_3_checked, root6Node73Step1Chunk4_4_checked, root6Node73Step1Chunk4_5_checked, root6Node73Step1Chunk5_0_checked, root6Node73Step1Chunk5_1_checked, root6Node73Step1Chunk5_2_checked, root6Node73Step1Chunk5_3_checked, root6Node73Step1Chunk5_4_checked, root6Node73Step1Chunk5_5_checked, root6Node73Step1Chunk6_0_checked, root6Node73Step1Chunk6_1_checked, root6Node73Step1Chunk6_2_checked, root6Node73Step1Chunk6_3_checked, root6Node73Step1Chunk6_4_checked, root6Node73Step1Chunk6_5_checked, root6Node73Step1Chunk7_0_checked, root6Node73Step1Chunk7_1_checked, root6Node73Step1Chunk7_2_checked, root6Node73Step1Chunk7_3_checked, root6Node73Step1Chunk7_4_checked, root6Node73Step1Chunk7_5_checked, root6Node73Step1Chunk8_0_checked, root6Node73Step1Chunk8_1_checked, root6Node73Step1Chunk8_2_checked, root6Node73Step1Chunk8_3_checked, root6Node73Step1Chunk8_4_checked, root6Node73Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node73Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,4)]
  | 1 => [(0,0)]
  | 2 => [(7,2)]
  | 3 => [(4,0)]
  | 4 => [(7,3)]
  | 5 => [(8,1)]
  | 6 => [(1,5)]
  | 7 => [(6,1)]
  | 8 => [(5,1)]
  | 9 => [(0,1)]
  | 10 => [(6,2)]
  | 11 => [(5,3)]
  | 12 => [(5,5)]
  | 13 => [(7,0)]
  | 14 => [(8,3)]
  | 15 => [(5,5)]
  | 16 => [(1,0)]
  | 17 => [(2,1)]
  | 18 => [(1,4)]
  | 19 => [(0,5)]
  | 20 => [(4,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(0,0)]
  | 25 => [(3,2)]
  | 26 => [(2,5)]
  | 27 => [(6,0)]
  | 28 => [(7,1)]
  | 29 => [(7,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(4,0)]
  | 37 => [(7,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(5,1)]
  | 44 => [(0,1)]
  | 45 => [(6,2)]
  | 46 => [(8,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(8,5)]
  | 51 => [(1,0)]
  | 52 => [(7,1)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(8,1)]
  | 56 => [(8,2)]
  | 57 => [(5,0)]
  | 58 => [(4,5)]
  | 59 => [(7,0)]
  | _ => [(8,3)]
def root6Node73Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,4)]
  | 1 => some [(0,0)]
  | 2 => some [(7,2)]
  | 3 => some [(4,0)]
  | 4 => some [(7,3)]
  | 5 => some [(8,1)]
  | 6 => some [(1,5)]
  | 7 => some [(6,1)]
  | 8 => some [(5,1)]
  | 9 => some [(0,1)]
  | 10 => some [(6,2)]
  | 11 => some [(5,3)]
  | 12 => some [(5,5)]
  | 13 => some [(7,0)]
  | 14 => some [(8,3)]
  | 15 => some [(5,5)]
  | 16 => some [(1,0)]
  | 17 => some [(2,1)]
  | 18 => some [(1,4)]
  | 19 => some [(0,5)]
  | 20 => some [(4,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(0,0)]
  | 25 => some [(3,2)]
  | 26 => some [(2,5)]
  | 27 => some [(6,0)]
  | 28 => some [(7,1)]
  | 29 => some [(7,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(4,0)]
  | 37 => some [(7,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(5,1)]
  | 44 => some [(0,1)]
  | 45 => some [(6,2)]
  | 46 => some [(8,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(8,5)]
  | 51 => some [(1,0)]
  | 52 => some [(7,1)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(8,1)]
  | 56 => some [(8,2)]
  | 57 => some [(5,0)]
  | 58 => some [(4,5)]
  | 59 => some [(7,0)]
  | _ => some [(8,3)]
theorem root6Node73Domains2_fast_eq : root6Node73Domains2 = expandDomains root6Node73Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node73Domains2 v = expandDomains root6Node73Domains2Fast v from by decide) v
theorem root6Node73Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root6Node73Domains1 root6Node73Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node73Domains1 root6Node73Domains2
    root6Node73Domains1Fast root6Node73Domains2Fast
    root6Node73Domains1_fast_eq root6Node73Domains2_fast_eq (by decide)
theorem root6Node73Step2_checked :
    checkReplacement table46 root6Node73Domains1 root6Node73Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node73Step2Chunk0_0_checked, root6Node73Step2Chunk0_1_checked, root6Node73Step2Chunk0_2_checked, root6Node73Step2Chunk0_3_checked, root6Node73Step2Chunk0_4_checked, root6Node73Step2Chunk0_5_checked, root6Node73Step2Chunk1_0_checked, root6Node73Step2Chunk1_1_checked, root6Node73Step2Chunk1_2_checked, root6Node73Step2Chunk1_3_checked, root6Node73Step2Chunk1_4_checked, root6Node73Step2Chunk1_5_checked, root6Node73Step2Chunk2_0_checked, root6Node73Step2Chunk2_1_checked, root6Node73Step2Chunk2_2_checked, root6Node73Step2Chunk2_3_checked, root6Node73Step2Chunk2_4_checked, root6Node73Step2Chunk2_5_checked, root6Node73Step2Chunk3_0_checked, root6Node73Step2Chunk3_1_checked, root6Node73Step2Chunk3_2_checked, root6Node73Step2Chunk3_3_checked, root6Node73Step2Chunk3_4_checked, root6Node73Step2Chunk3_5_checked, root6Node73Step2Chunk4_0_checked, root6Node73Step2Chunk4_1_checked, root6Node73Step2Chunk4_2_checked, root6Node73Step2Chunk4_3_checked, root6Node73Step2Chunk4_4_checked, root6Node73Step2Chunk4_5_checked, root6Node73Step2Chunk5_0_checked, root6Node73Step2Chunk5_1_checked, root6Node73Step2Chunk5_2_checked, root6Node73Step2Chunk5_3_checked, root6Node73Step2Chunk5_4_checked, root6Node73Step2Chunk5_5_checked, root6Node73Step2Chunk6_0_checked, root6Node73Step2Chunk6_1_checked, root6Node73Step2Chunk6_2_checked, root6Node73Step2Chunk6_3_checked, root6Node73Step2Chunk6_4_checked, root6Node73Step2Chunk6_5_checked, root6Node73Step2Chunk7_0_checked, root6Node73Step2Chunk7_1_checked, root6Node73Step2Chunk7_2_checked, root6Node73Step2Chunk7_3_checked, root6Node73Step2Chunk7_4_checked, root6Node73Step2Chunk7_5_checked, root6Node73Step2Chunk8_0_checked, root6Node73Step2Chunk8_1_checked, root6Node73Step2Chunk8_2_checked, root6Node73Step2Chunk8_3_checked, root6Node73Step2Chunk8_4_checked, root6Node73Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root6Node73Leaf_checked :
    checkCover 1 constraints root6Outputs root6Node73Domains2 (.output 36) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
