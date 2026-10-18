module

public import SpectreFinite.RadiusFourRoot6Part0
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable10
public import SpectreFinite.RadiusFourTable16
public import SpectreFinite.RadiusFourTable20
public import SpectreFinite.RadiusFourTable35
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root6Node1Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(4,0),(5,0),(7,4),(8,0),(8,4)]
  | 4 => [(0,0),(1,3),(4,5),(7,3)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(8,1)]
  | 9 => [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 10 => [(0,4),(1,2),(6,1),(6,2),(7,2)]
  | 11 => [(7,4)]
  | 12 => [(1,3)]
  | 13 => [(4,2)]
  | 14 => [(5,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(2,1),(2,3),(2,5),(4,1),(4,3),(8,3)]
  | 18 => [(8,1)]
  | 19 => [(6,5)]
  | 20 => [(0,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 26 => [(8,3)]
  | 27 => [(5,5)]
  | 28 => [(3,0)]
  | 29 => [(2,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0),(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5),(5,5),(7,5),(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(4,2),(4,4),(7,2),(8,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3),(6,3)]
  | 59 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root6Node1Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(4,0),(5,0),(7,4),(8,0),(8,4)]
  | 4 => some [(0,0),(1,3),(4,5),(7,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(0,0),(0,1),(1,5),(6,4),(6,5)]
  | 10 => some [(0,4),(1,2),(6,1),(6,2),(7,2)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(2,1),(2,3),(2,5),(4,1),(4,3),(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5),(1,2),(3,2),(5,2),(7,2)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1),(5,1),(5,4),(7,1),(8,4)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5),(5,5),(7,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root6Node1Domains2_fast_eq : root6Node1Domains2 = expandDomains root6Node1Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node1Domains2 v = expandDomains root6Node1Domains2Fast v from by decide) v
theorem root6Node1Step2Chunk0_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk0_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk1_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk2_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk3_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk4_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk5_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk6_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk7_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_0⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_1⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_2⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_3⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_4⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2Chunk8_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_5⟩
      root6Node1Domains1 root6Node1Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains1 root6Node1Domains2
    root6Node1Domains1Fast root6Node1Domains2Fast
    root6Node1Domains1_fast_eq root6Node1Domains2_fast_eq (by decide)
theorem root6Node1Step2_checked :
    checkReplacement table20 root6Node1Domains1 root6Node1Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node1Step2Chunk0_0_checked, root6Node1Step2Chunk0_1_checked, root6Node1Step2Chunk0_2_checked, root6Node1Step2Chunk0_3_checked, root6Node1Step2Chunk0_4_checked, root6Node1Step2Chunk0_5_checked, root6Node1Step2Chunk1_0_checked, root6Node1Step2Chunk1_1_checked, root6Node1Step2Chunk1_2_checked, root6Node1Step2Chunk1_3_checked, root6Node1Step2Chunk1_4_checked, root6Node1Step2Chunk1_5_checked, root6Node1Step2Chunk2_0_checked, root6Node1Step2Chunk2_1_checked, root6Node1Step2Chunk2_2_checked, root6Node1Step2Chunk2_3_checked, root6Node1Step2Chunk2_4_checked, root6Node1Step2Chunk2_5_checked, root6Node1Step2Chunk3_0_checked, root6Node1Step2Chunk3_1_checked, root6Node1Step2Chunk3_2_checked, root6Node1Step2Chunk3_3_checked, root6Node1Step2Chunk3_4_checked, root6Node1Step2Chunk3_5_checked, root6Node1Step2Chunk4_0_checked, root6Node1Step2Chunk4_1_checked, root6Node1Step2Chunk4_2_checked, root6Node1Step2Chunk4_3_checked, root6Node1Step2Chunk4_4_checked, root6Node1Step2Chunk4_5_checked, root6Node1Step2Chunk5_0_checked, root6Node1Step2Chunk5_1_checked, root6Node1Step2Chunk5_2_checked, root6Node1Step2Chunk5_3_checked, root6Node1Step2Chunk5_4_checked, root6Node1Step2Chunk5_5_checked, root6Node1Step2Chunk6_0_checked, root6Node1Step2Chunk6_1_checked, root6Node1Step2Chunk6_2_checked, root6Node1Step2Chunk6_3_checked, root6Node1Step2Chunk6_4_checked, root6Node1Step2Chunk6_5_checked, root6Node1Step2Chunk7_0_checked, root6Node1Step2Chunk7_1_checked, root6Node1Step2Chunk7_2_checked, root6Node1Step2Chunk7_3_checked, root6Node1Step2Chunk7_4_checked, root6Node1Step2Chunk7_5_checked, root6Node1Step2Chunk8_0_checked, root6Node1Step2Chunk8_1_checked, root6Node1Step2Chunk8_2_checked, root6Node1Step2Chunk8_3_checked, root6Node1Step2Chunk8_4_checked, root6Node1Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node1Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4),(8,4)]
  | 4 => [(0,0),(1,3)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(8,1)]
  | 9 => [(1,5),(6,5)]
  | 10 => [(0,4),(6,1)]
  | 11 => [(7,4)]
  | 12 => [(1,3)]
  | 13 => [(4,2)]
  | 14 => [(5,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(4,3),(8,3)]
  | 18 => [(8,1)]
  | 19 => [(6,5)]
  | 20 => [(0,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(8,3)]
  | 27 => [(5,5)]
  | 28 => [(3,0)]
  | 29 => [(2,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(3,1),(7,1)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0),(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5),(5,5),(7,5),(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(4,2),(4,4),(7,2),(8,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3),(6,3)]
  | 59 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root6Node1Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4),(8,4)]
  | 4 => some [(0,0),(1,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(1,5),(6,5)]
  | 10 => some [(0,4),(6,1)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(4,3),(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1),(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5),(5,5),(7,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(4,2),(4,4),(7,2),(8,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root6Node1Domains3_fast_eq : root6Node1Domains3 = expandDomains root6Node1Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node1Domains3 v = expandDomains root6Node1Domains3Fast v from by decide) v
theorem root6Node1Step3Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root6Node1Domains2 root6Node1Domains3 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains2 root6Node1Domains3
    root6Node1Domains2Fast root6Node1Domains3Fast
    root6Node1Domains2_fast_eq root6Node1Domains3_fast_eq (by decide)
theorem root6Node1Step3_checked :
    checkReplacement table10 root6Node1Domains2 root6Node1Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node1Step3Chunk0_0_checked, root6Node1Step3Chunk0_1_checked, root6Node1Step3Chunk0_2_checked, root6Node1Step3Chunk0_3_checked, root6Node1Step3Chunk0_4_checked, root6Node1Step3Chunk0_5_checked, root6Node1Step3Chunk1_0_checked, root6Node1Step3Chunk1_1_checked, root6Node1Step3Chunk1_2_checked, root6Node1Step3Chunk1_3_checked, root6Node1Step3Chunk1_4_checked, root6Node1Step3Chunk1_5_checked, root6Node1Step3Chunk2_0_checked, root6Node1Step3Chunk2_1_checked, root6Node1Step3Chunk2_2_checked, root6Node1Step3Chunk2_3_checked, root6Node1Step3Chunk2_4_checked, root6Node1Step3Chunk2_5_checked, root6Node1Step3Chunk3_0_checked, root6Node1Step3Chunk3_1_checked, root6Node1Step3Chunk3_2_checked, root6Node1Step3Chunk3_3_checked, root6Node1Step3Chunk3_4_checked, root6Node1Step3Chunk3_5_checked, root6Node1Step3Chunk4_0_checked, root6Node1Step3Chunk4_1_checked, root6Node1Step3Chunk4_2_checked, root6Node1Step3Chunk4_3_checked, root6Node1Step3Chunk4_4_checked, root6Node1Step3Chunk4_5_checked, root6Node1Step3Chunk5_0_checked, root6Node1Step3Chunk5_1_checked, root6Node1Step3Chunk5_2_checked, root6Node1Step3Chunk5_3_checked, root6Node1Step3Chunk5_4_checked, root6Node1Step3Chunk5_5_checked, root6Node1Step3Chunk6_0_checked, root6Node1Step3Chunk6_1_checked, root6Node1Step3Chunk6_2_checked, root6Node1Step3Chunk6_3_checked, root6Node1Step3Chunk6_4_checked, root6Node1Step3Chunk6_5_checked, root6Node1Step3Chunk7_0_checked, root6Node1Step3Chunk7_1_checked, root6Node1Step3Chunk7_2_checked, root6Node1Step3Chunk7_3_checked, root6Node1Step3Chunk7_4_checked, root6Node1Step3Chunk7_5_checked, root6Node1Step3Chunk8_0_checked, root6Node1Step3Chunk8_1_checked, root6Node1Step3Chunk8_2_checked, root6Node1Step3Chunk8_3_checked, root6Node1Step3Chunk8_4_checked, root6Node1Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node1Domains4 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4),(8,4)]
  | 4 => [(0,0),(1,3)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(8,1)]
  | 9 => [(1,5),(6,5)]
  | 10 => [(0,4),(6,1)]
  | 11 => [(7,4)]
  | 12 => [(1,3)]
  | 13 => [(4,2)]
  | 14 => [(5,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(4,3),(8,3)]
  | 18 => [(8,1)]
  | 19 => [(6,5)]
  | 20 => [(0,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(8,3)]
  | 27 => [(5,5)]
  | 28 => [(3,0)]
  | 29 => [(2,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(3,1),(7,1)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0),(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3),(6,3)]
  | 59 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root6Node1Domains4Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4),(8,4)]
  | 4 => some [(0,0),(1,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(1,5),(6,5)]
  | 10 => some [(0,4),(6,1)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(4,3),(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1),(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root6Node1Domains4_fast_eq : root6Node1Domains4 = expandDomains root6Node1Domains4Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node1Domains4 v = expandDomains root6Node1Domains4Fast v from by decide) v
theorem root6Node1Step4Chunk0_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk0_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows0_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk1_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows1_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk2_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows2_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk3_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows3_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk4_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows4_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk5_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows5_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk6_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows6_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk7_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows7_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_0_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_0⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_1_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_1⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_2_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_2⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_3_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_3⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_4_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_4⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4Chunk8_5_checked :
    checkNarrowing ⟨table35Scope, table35Rows8_5⟩
      root6Node1Domains3 root6Node1Domains4 = true := by
  exact checkNarrowing_of_fast _ root6Node1Domains3 root6Node1Domains4
    root6Node1Domains3Fast root6Node1Domains4Fast
    root6Node1Domains3_fast_eq root6Node1Domains4_fast_eq (by decide)
theorem root6Node1Step4_checked :
    checkReplacement table35 root6Node1Domains3 root6Node1Domains4 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node1Step4Chunk0_0_checked, root6Node1Step4Chunk0_1_checked, root6Node1Step4Chunk0_2_checked, root6Node1Step4Chunk0_3_checked, root6Node1Step4Chunk0_4_checked, root6Node1Step4Chunk0_5_checked, root6Node1Step4Chunk1_0_checked, root6Node1Step4Chunk1_1_checked, root6Node1Step4Chunk1_2_checked, root6Node1Step4Chunk1_3_checked, root6Node1Step4Chunk1_4_checked, root6Node1Step4Chunk1_5_checked, root6Node1Step4Chunk2_0_checked, root6Node1Step4Chunk2_1_checked, root6Node1Step4Chunk2_2_checked, root6Node1Step4Chunk2_3_checked, root6Node1Step4Chunk2_4_checked, root6Node1Step4Chunk2_5_checked, root6Node1Step4Chunk3_0_checked, root6Node1Step4Chunk3_1_checked, root6Node1Step4Chunk3_2_checked, root6Node1Step4Chunk3_3_checked, root6Node1Step4Chunk3_4_checked, root6Node1Step4Chunk3_5_checked, root6Node1Step4Chunk4_0_checked, root6Node1Step4Chunk4_1_checked, root6Node1Step4Chunk4_2_checked, root6Node1Step4Chunk4_3_checked, root6Node1Step4Chunk4_4_checked, root6Node1Step4Chunk4_5_checked, root6Node1Step4Chunk5_0_checked, root6Node1Step4Chunk5_1_checked, root6Node1Step4Chunk5_2_checked, root6Node1Step4Chunk5_3_checked, root6Node1Step4Chunk5_4_checked, root6Node1Step4Chunk5_5_checked, root6Node1Step4Chunk6_0_checked, root6Node1Step4Chunk6_1_checked, root6Node1Step4Chunk6_2_checked, root6Node1Step4Chunk6_3_checked, root6Node1Step4Chunk6_4_checked, root6Node1Step4Chunk6_5_checked, root6Node1Step4Chunk7_0_checked, root6Node1Step4Chunk7_1_checked, root6Node1Step4Chunk7_2_checked, root6Node1Step4Chunk7_3_checked, root6Node1Step4Chunk7_4_checked, root6Node1Step4Chunk7_5_checked, root6Node1Step4Chunk8_0_checked, root6Node1Step4Chunk8_1_checked, root6Node1Step4Chunk8_2_checked, root6Node1Step4Chunk8_3_checked, root6Node1Step4Chunk8_4_checked, root6Node1Step4Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node2Domains0 : Domains 61 State := restrict root6Node1Domains4 3 (7,4)
def root6Node2Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(0,0),(1,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(1,5),(6,5)]
  | 10 => some [(0,4),(6,1)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(4,3),(8,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1),(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root6Node2Domains0_fast_eq : root6Node2Domains0 = expandDomains root6Node2Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node2Domains0 v = expandDomains root6Node2Domains0Fast v from by decide) v
def root6Node2Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(7,4)]
  | 12 => [(1,3)]
  | 13 => [(4,2)]
  | 14 => [(5,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(4,3)]
  | 18 => [(8,1)]
  | 19 => [(6,5)]
  | 20 => [(0,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(8,3)]
  | 27 => [(5,5)]
  | 28 => [(3,0)]
  | 29 => [(2,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(3,1),(7,1)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3),(6,3)]
  | 59 => [(7,2),(8,2)]
  | _ => [(4,0),(5,0),(8,0)]
def root6Node2Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(4,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1),(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3),(6,3)]
  | 59 => some [(7,2),(8,2)]
  | _ => some [(4,0),(5,0),(8,0)]
theorem root6Node2Domains1_fast_eq : root6Node2Domains1 = expandDomains root6Node2Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node2Domains1 v = expandDomains root6Node2Domains1Fast v from by decide) v
theorem root6Node2Step1Chunk0_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk0_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk0_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk0_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk0_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk0_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows0_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk1_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows1_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk2_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows2_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk3_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows3_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk4_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows4_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk5_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows5_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk6_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows6_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk7_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows7_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_0_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_0⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_1_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_1⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_2_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_2⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_3_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_3⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_4_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_4⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1Chunk8_5_checked :
    checkNarrowing ⟨table16Scope, table16Rows8_5⟩
      root6Node2Domains0 root6Node2Domains1 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains0 root6Node2Domains1
    root6Node2Domains0Fast root6Node2Domains1Fast
    root6Node2Domains0_fast_eq root6Node2Domains1_fast_eq (by decide)
theorem root6Node2Step1_checked :
    checkReplacement table16 root6Node2Domains0 root6Node2Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node2Step1Chunk0_0_checked, root6Node2Step1Chunk0_1_checked, root6Node2Step1Chunk0_2_checked, root6Node2Step1Chunk0_3_checked, root6Node2Step1Chunk0_4_checked, root6Node2Step1Chunk0_5_checked, root6Node2Step1Chunk1_0_checked, root6Node2Step1Chunk1_1_checked, root6Node2Step1Chunk1_2_checked, root6Node2Step1Chunk1_3_checked, root6Node2Step1Chunk1_4_checked, root6Node2Step1Chunk1_5_checked, root6Node2Step1Chunk2_0_checked, root6Node2Step1Chunk2_1_checked, root6Node2Step1Chunk2_2_checked, root6Node2Step1Chunk2_3_checked, root6Node2Step1Chunk2_4_checked, root6Node2Step1Chunk2_5_checked, root6Node2Step1Chunk3_0_checked, root6Node2Step1Chunk3_1_checked, root6Node2Step1Chunk3_2_checked, root6Node2Step1Chunk3_3_checked, root6Node2Step1Chunk3_4_checked, root6Node2Step1Chunk3_5_checked, root6Node2Step1Chunk4_0_checked, root6Node2Step1Chunk4_1_checked, root6Node2Step1Chunk4_2_checked, root6Node2Step1Chunk4_3_checked, root6Node2Step1Chunk4_4_checked, root6Node2Step1Chunk4_5_checked, root6Node2Step1Chunk5_0_checked, root6Node2Step1Chunk5_1_checked, root6Node2Step1Chunk5_2_checked, root6Node2Step1Chunk5_3_checked, root6Node2Step1Chunk5_4_checked, root6Node2Step1Chunk5_5_checked, root6Node2Step1Chunk6_0_checked, root6Node2Step1Chunk6_1_checked, root6Node2Step1Chunk6_2_checked, root6Node2Step1Chunk6_3_checked, root6Node2Step1Chunk6_4_checked, root6Node2Step1Chunk6_5_checked, root6Node2Step1Chunk7_0_checked, root6Node2Step1Chunk7_1_checked, root6Node2Step1Chunk7_2_checked, root6Node2Step1Chunk7_3_checked, root6Node2Step1Chunk7_4_checked, root6Node2Step1Chunk7_5_checked, root6Node2Step1Chunk8_0_checked, root6Node2Step1Chunk8_1_checked, root6Node2Step1Chunk8_2_checked, root6Node2Step1Chunk8_3_checked, root6Node2Step1Chunk8_4_checked, root6Node2Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root6Node2Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,4)]
  | 1 => [(6,4)]
  | 2 => [(1,2)]
  | 3 => [(7,4)]
  | 4 => [(1,3)]
  | 5 => [(4,3)]
  | 6 => [(7,5)]
  | 7 => [(0,3)]
  | 8 => [(8,1)]
  | 9 => [(6,5)]
  | 10 => [(0,4)]
  | 11 => [(7,4)]
  | 12 => [(1,3)]
  | 13 => [(4,2)]
  | 14 => [(5,3)]
  | 15 => [(5,5)]
  | 16 => [(7,0)]
  | 17 => [(4,3)]
  | 18 => [(8,1)]
  | 19 => [(6,5)]
  | 20 => [(0,4)]
  | 21 => [(1,4)]
  | 22 => [(0,5)]
  | 23 => [(4,4)]
  | 24 => [(1,4)]
  | 25 => [(0,5)]
  | 26 => [(8,3)]
  | 27 => [(5,5)]
  | 28 => [(3,0)]
  | 29 => [(2,5)]
  | 30 => [(6,0)]
  | 31 => [(7,1)]
  | 32 => [(7,5)]
  | 33 => [(6,0)]
  | 34 => [(3,1),(7,1)]
  | 35 => [(0,5)]
  | 36 => [(4,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(4,0)]
  | 40 => [(7,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(5,1)]
  | 47 => [(0,1)]
  | 48 => [(6,2)]
  | 49 => [(8,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(1,0)]
  | 55 => [(7,1)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(1,3)]
  | 59 => [(8,2)]
  | _ => [(5,0)]
def root6Node2Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,4)]
  | 1 => some [(6,4)]
  | 2 => some [(1,2)]
  | 3 => some [(7,4)]
  | 4 => some [(1,3)]
  | 5 => some [(4,3)]
  | 6 => some [(7,5)]
  | 7 => some [(0,3)]
  | 8 => some [(8,1)]
  | 9 => some [(6,5)]
  | 10 => some [(0,4)]
  | 11 => some [(7,4)]
  | 12 => some [(1,3)]
  | 13 => some [(4,2)]
  | 14 => some [(5,3)]
  | 15 => some [(5,5)]
  | 16 => some [(7,0)]
  | 17 => some [(4,3)]
  | 18 => some [(8,1)]
  | 19 => some [(6,5)]
  | 20 => some [(0,4)]
  | 21 => some [(1,4)]
  | 22 => some [(0,5)]
  | 23 => some [(4,4)]
  | 24 => some [(1,4)]
  | 25 => some [(0,5)]
  | 26 => some [(8,3)]
  | 27 => some [(5,5)]
  | 28 => some [(3,0)]
  | 29 => some [(2,5)]
  | 30 => some [(6,0)]
  | 31 => some [(7,1)]
  | 32 => some [(7,5)]
  | 33 => some [(6,0)]
  | 34 => some [(3,1),(7,1)]
  | 35 => some [(0,5)]
  | 36 => some [(4,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(4,0)]
  | 40 => some [(7,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(5,1)]
  | 47 => some [(0,1)]
  | 48 => some [(6,2)]
  | 49 => some [(8,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(1,0)]
  | 55 => some [(7,1)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(1,3)]
  | 59 => some [(8,2)]
  | _ => some [(5,0)]
theorem root6Node2Domains2_fast_eq : root6Node2Domains2 = expandDomains root6Node2Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root6Node2Domains2 v = expandDomains root6Node2Domains2Fast v from by decide) v
theorem root6Node2Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root6Node2Domains1 root6Node2Domains2 = true := by
  exact checkNarrowing_of_fast _ root6Node2Domains1 root6Node2Domains2
    root6Node2Domains1Fast root6Node2Domains2Fast
    root6Node2Domains1_fast_eq root6Node2Domains2_fast_eq (by decide)
theorem root6Node2Step2_checked :
    checkReplacement table39 root6Node2Domains1 root6Node2Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root6Node2Step2Chunk0_0_checked, root6Node2Step2Chunk0_1_checked, root6Node2Step2Chunk0_2_checked, root6Node2Step2Chunk0_3_checked, root6Node2Step2Chunk0_4_checked, root6Node2Step2Chunk0_5_checked, root6Node2Step2Chunk1_0_checked, root6Node2Step2Chunk1_1_checked, root6Node2Step2Chunk1_2_checked, root6Node2Step2Chunk1_3_checked, root6Node2Step2Chunk1_4_checked, root6Node2Step2Chunk1_5_checked, root6Node2Step2Chunk2_0_checked, root6Node2Step2Chunk2_1_checked, root6Node2Step2Chunk2_2_checked, root6Node2Step2Chunk2_3_checked, root6Node2Step2Chunk2_4_checked, root6Node2Step2Chunk2_5_checked, root6Node2Step2Chunk3_0_checked, root6Node2Step2Chunk3_1_checked, root6Node2Step2Chunk3_2_checked, root6Node2Step2Chunk3_3_checked, root6Node2Step2Chunk3_4_checked, root6Node2Step2Chunk3_5_checked, root6Node2Step2Chunk4_0_checked, root6Node2Step2Chunk4_1_checked, root6Node2Step2Chunk4_2_checked, root6Node2Step2Chunk4_3_checked, root6Node2Step2Chunk4_4_checked, root6Node2Step2Chunk4_5_checked, root6Node2Step2Chunk5_0_checked, root6Node2Step2Chunk5_1_checked, root6Node2Step2Chunk5_2_checked, root6Node2Step2Chunk5_3_checked, root6Node2Step2Chunk5_4_checked, root6Node2Step2Chunk5_5_checked, root6Node2Step2Chunk6_0_checked, root6Node2Step2Chunk6_1_checked, root6Node2Step2Chunk6_2_checked, root6Node2Step2Chunk6_3_checked, root6Node2Step2Chunk6_4_checked, root6Node2Step2Chunk6_5_checked, root6Node2Step2Chunk7_0_checked, root6Node2Step2Chunk7_1_checked, root6Node2Step2Chunk7_2_checked, root6Node2Step2Chunk7_3_checked, root6Node2Step2Chunk7_4_checked, root6Node2Step2Chunk7_5_checked, root6Node2Step2Chunk8_0_checked, root6Node2Step2Chunk8_1_checked, root6Node2Step2Chunk8_2_checked, root6Node2Step2Chunk8_3_checked, root6Node2Step2Chunk8_4_checked, root6Node2Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
