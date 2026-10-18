module

public import SpectreFinite.RadiusFourRoot8Part19
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable20
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable40
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node63Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,0),(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(4,2),(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4),(7,2)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(6,3)]
  | 53 => [(2,2),(2,4)]
  | 54 => [(1,3),(3,3)]
  | 55 => [(5,2)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(1,1),(7,1)]
  | 59 => [(0,1),(6,5)]
  | _ => [(0,4),(6,2)]
def root8Node63Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0),(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(6,3)]
  | 53 => some [(2,2),(2,4)]
  | 54 => some [(1,3),(3,3)]
  | 55 => some [(5,2)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(1,1),(7,1)]
  | 59 => some [(0,1),(6,5)]
  | _ => some [(0,4),(6,2)]
theorem root8Node63Domains2_fast_eq : root8Node63Domains2 = expandDomains root8Node63Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node63Domains2 v = expandDomains root8Node63Domains2Fast v from by decide) v
theorem root8Node63Step2Chunk0_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_0⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk0_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_1⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk0_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_2⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk0_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_3⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk0_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_4⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk0_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows0_5⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk1_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_0⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk1_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_1⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk1_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_2⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk1_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_3⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk1_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_4⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk1_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows1_5⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk2_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_0⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk2_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_1⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk2_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_2⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk2_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_3⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk2_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_4⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk2_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows2_5⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk3_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_0⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk3_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_1⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk3_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_2⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk3_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_3⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk3_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_4⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk3_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows3_5⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk4_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_0⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk4_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_1⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk4_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_2⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk4_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_3⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk4_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_4⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk4_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows4_5⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk5_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_0⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk5_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_1⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk5_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_2⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk5_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_3⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk5_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_4⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk5_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows5_5⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk6_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_0⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk6_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_1⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk6_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_2⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk6_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_3⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk6_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_4⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk6_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows6_5⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk7_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_0⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk7_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_1⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk7_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_2⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk7_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_3⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk7_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_4⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk7_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows7_5⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk8_0_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_0⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk8_1_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_1⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk8_2_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_2⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk8_3_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_3⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk8_4_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_4⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2Chunk8_5_checked :
    checkNarrowing ⟨table40Scope, table40Rows8_5⟩
      root8Node63Domains1 root8Node63Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains1 root8Node63Domains2
    root8Node63Domains1Fast root8Node63Domains2Fast
    root8Node63Domains1_fast_eq root8Node63Domains2_fast_eq (by decide)
theorem root8Node63Step2_checked :
    checkReplacement table40 root8Node63Domains1 root8Node63Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node63Step2Chunk0_0_checked, root8Node63Step2Chunk0_1_checked, root8Node63Step2Chunk0_2_checked, root8Node63Step2Chunk0_3_checked, root8Node63Step2Chunk0_4_checked, root8Node63Step2Chunk0_5_checked, root8Node63Step2Chunk1_0_checked, root8Node63Step2Chunk1_1_checked, root8Node63Step2Chunk1_2_checked, root8Node63Step2Chunk1_3_checked, root8Node63Step2Chunk1_4_checked, root8Node63Step2Chunk1_5_checked, root8Node63Step2Chunk2_0_checked, root8Node63Step2Chunk2_1_checked, root8Node63Step2Chunk2_2_checked, root8Node63Step2Chunk2_3_checked, root8Node63Step2Chunk2_4_checked, root8Node63Step2Chunk2_5_checked, root8Node63Step2Chunk3_0_checked, root8Node63Step2Chunk3_1_checked, root8Node63Step2Chunk3_2_checked, root8Node63Step2Chunk3_3_checked, root8Node63Step2Chunk3_4_checked, root8Node63Step2Chunk3_5_checked, root8Node63Step2Chunk4_0_checked, root8Node63Step2Chunk4_1_checked, root8Node63Step2Chunk4_2_checked, root8Node63Step2Chunk4_3_checked, root8Node63Step2Chunk4_4_checked, root8Node63Step2Chunk4_5_checked, root8Node63Step2Chunk5_0_checked, root8Node63Step2Chunk5_1_checked, root8Node63Step2Chunk5_2_checked, root8Node63Step2Chunk5_3_checked, root8Node63Step2Chunk5_4_checked, root8Node63Step2Chunk5_5_checked, root8Node63Step2Chunk6_0_checked, root8Node63Step2Chunk6_1_checked, root8Node63Step2Chunk6_2_checked, root8Node63Step2Chunk6_3_checked, root8Node63Step2Chunk6_4_checked, root8Node63Step2Chunk6_5_checked, root8Node63Step2Chunk7_0_checked, root8Node63Step2Chunk7_1_checked, root8Node63Step2Chunk7_2_checked, root8Node63Step2Chunk7_3_checked, root8Node63Step2Chunk7_4_checked, root8Node63Step2Chunk7_5_checked, root8Node63Step2Chunk8_0_checked, root8Node63Step2Chunk8_1_checked, root8Node63Step2Chunk8_2_checked, root8Node63Step2Chunk8_3_checked, root8Node63Step2Chunk8_4_checked, root8Node63Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node63Domains3 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,0),(6,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(8,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4),(7,2)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(6,3)]
  | 53 => [(2,2),(2,4)]
  | 54 => [(1,3),(3,3)]
  | 55 => [(5,2)]
  | 56 => [(4,1),(7,5)]
  | 57 => [(0,2),(6,0)]
  | 58 => [(1,1),(7,1)]
  | 59 => [(0,1),(6,5)]
  | _ => [(0,4),(6,2)]
def root8Node63Domains3Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0),(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(6,3)]
  | 53 => some [(2,2),(2,4)]
  | 54 => some [(1,3),(3,3)]
  | 55 => some [(5,2)]
  | 56 => some [(4,1),(7,5)]
  | 57 => some [(0,2),(6,0)]
  | 58 => some [(1,1),(7,1)]
  | 59 => some [(0,1),(6,5)]
  | _ => some [(0,4),(6,2)]
theorem root8Node63Domains3_fast_eq : root8Node63Domains3 = expandDomains root8Node63Domains3Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node63Domains3 v = expandDomains root8Node63Domains3Fast v from by decide) v
theorem root8Node63Step3Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root8Node63Domains2 root8Node63Domains3 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains2 root8Node63Domains3
    root8Node63Domains2Fast root8Node63Domains3Fast
    root8Node63Domains2_fast_eq root8Node63Domains3_fast_eq (by decide)
theorem root8Node63Step3_checked :
    checkReplacement table36 root8Node63Domains2 root8Node63Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node63Step3Chunk0_0_checked, root8Node63Step3Chunk0_1_checked, root8Node63Step3Chunk0_2_checked, root8Node63Step3Chunk0_3_checked, root8Node63Step3Chunk0_4_checked, root8Node63Step3Chunk0_5_checked, root8Node63Step3Chunk1_0_checked, root8Node63Step3Chunk1_1_checked, root8Node63Step3Chunk1_2_checked, root8Node63Step3Chunk1_3_checked, root8Node63Step3Chunk1_4_checked, root8Node63Step3Chunk1_5_checked, root8Node63Step3Chunk2_0_checked, root8Node63Step3Chunk2_1_checked, root8Node63Step3Chunk2_2_checked, root8Node63Step3Chunk2_3_checked, root8Node63Step3Chunk2_4_checked, root8Node63Step3Chunk2_5_checked, root8Node63Step3Chunk3_0_checked, root8Node63Step3Chunk3_1_checked, root8Node63Step3Chunk3_2_checked, root8Node63Step3Chunk3_3_checked, root8Node63Step3Chunk3_4_checked, root8Node63Step3Chunk3_5_checked, root8Node63Step3Chunk4_0_checked, root8Node63Step3Chunk4_1_checked, root8Node63Step3Chunk4_2_checked, root8Node63Step3Chunk4_3_checked, root8Node63Step3Chunk4_4_checked, root8Node63Step3Chunk4_5_checked, root8Node63Step3Chunk5_0_checked, root8Node63Step3Chunk5_1_checked, root8Node63Step3Chunk5_2_checked, root8Node63Step3Chunk5_3_checked, root8Node63Step3Chunk5_4_checked, root8Node63Step3Chunk5_5_checked, root8Node63Step3Chunk6_0_checked, root8Node63Step3Chunk6_1_checked, root8Node63Step3Chunk6_2_checked, root8Node63Step3Chunk6_3_checked, root8Node63Step3Chunk6_4_checked, root8Node63Step3Chunk6_5_checked, root8Node63Step3Chunk7_0_checked, root8Node63Step3Chunk7_1_checked, root8Node63Step3Chunk7_2_checked, root8Node63Step3Chunk7_3_checked, root8Node63Step3Chunk7_4_checked, root8Node63Step3Chunk7_5_checked, root8Node63Step3Chunk8_0_checked, root8Node63Step3Chunk8_1_checked, root8Node63Step3Chunk8_2_checked, root8Node63Step3Chunk8_3_checked, root8Node63Step3Chunk8_4_checked, root8Node63Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node64Domains0 : Domains 61 State := restrict root8Node63Domains3 0 (1,0)
def root8Node64Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(6,3)]
  | 53 => some [(2,2),(2,4)]
  | 54 => some [(1,3),(3,3)]
  | 55 => some [(5,2)]
  | 56 => some [(4,1),(7,5)]
  | 57 => some [(0,2),(6,0)]
  | 58 => some [(1,1),(7,1)]
  | 59 => some [(0,1),(6,5)]
  | _ => some [(0,4),(6,2)]
theorem root8Node64Domains0_fast_eq : root8Node64Domains0 = expandDomains root8Node64Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node64Domains0 v = expandDomains root8Node64Domains0Fast v from by decide) v
def root8Node64Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(8,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(3,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4),(7,2)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(6,3)]
  | 53 => [(2,2),(2,4)]
  | 54 => [(1,3),(3,3)]
  | 55 => [(5,2)]
  | 56 => [(4,1),(7,5)]
  | 57 => [(0,2),(6,0)]
  | 58 => [(1,1),(7,1)]
  | 59 => [(0,1),(6,5)]
  | _ => [(0,4),(6,2)]
def root8Node64Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(6,3)]
  | 53 => some [(2,2),(2,4)]
  | 54 => some [(1,3),(3,3)]
  | 55 => some [(5,2)]
  | 56 => some [(4,1),(7,5)]
  | 57 => some [(0,2),(6,0)]
  | 58 => some [(1,1),(7,1)]
  | 59 => some [(0,1),(6,5)]
  | _ => some [(0,4),(6,2)]
theorem root8Node64Domains1_fast_eq : root8Node64Domains1 = expandDomains root8Node64Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node64Domains1 v = expandDomains root8Node64Domains1Fast v from by decide) v
theorem root8Node64Step1Chunk0_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk0_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk0_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk0_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk0_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk0_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows0_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk1_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows1_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk2_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows2_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk3_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows3_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk4_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows4_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk5_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows5_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk6_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows6_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk7_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows7_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_0_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_0⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_1_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_1⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_2_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_2⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_3_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_3⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_4_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_4⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1Chunk8_5_checked :
    checkNarrowing ⟨table20Scope, table20Rows8_5⟩
      root8Node64Domains0 root8Node64Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains0 root8Node64Domains1
    root8Node64Domains0Fast root8Node64Domains1Fast
    root8Node64Domains0_fast_eq root8Node64Domains1_fast_eq (by decide)
theorem root8Node64Step1_checked :
    checkReplacement table20 root8Node64Domains0 root8Node64Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node64Step1Chunk0_0_checked, root8Node64Step1Chunk0_1_checked, root8Node64Step1Chunk0_2_checked, root8Node64Step1Chunk0_3_checked, root8Node64Step1Chunk0_4_checked, root8Node64Step1Chunk0_5_checked, root8Node64Step1Chunk1_0_checked, root8Node64Step1Chunk1_1_checked, root8Node64Step1Chunk1_2_checked, root8Node64Step1Chunk1_3_checked, root8Node64Step1Chunk1_4_checked, root8Node64Step1Chunk1_5_checked, root8Node64Step1Chunk2_0_checked, root8Node64Step1Chunk2_1_checked, root8Node64Step1Chunk2_2_checked, root8Node64Step1Chunk2_3_checked, root8Node64Step1Chunk2_4_checked, root8Node64Step1Chunk2_5_checked, root8Node64Step1Chunk3_0_checked, root8Node64Step1Chunk3_1_checked, root8Node64Step1Chunk3_2_checked, root8Node64Step1Chunk3_3_checked, root8Node64Step1Chunk3_4_checked, root8Node64Step1Chunk3_5_checked, root8Node64Step1Chunk4_0_checked, root8Node64Step1Chunk4_1_checked, root8Node64Step1Chunk4_2_checked, root8Node64Step1Chunk4_3_checked, root8Node64Step1Chunk4_4_checked, root8Node64Step1Chunk4_5_checked, root8Node64Step1Chunk5_0_checked, root8Node64Step1Chunk5_1_checked, root8Node64Step1Chunk5_2_checked, root8Node64Step1Chunk5_3_checked, root8Node64Step1Chunk5_4_checked, root8Node64Step1Chunk5_5_checked, root8Node64Step1Chunk6_0_checked, root8Node64Step1Chunk6_1_checked, root8Node64Step1Chunk6_2_checked, root8Node64Step1Chunk6_3_checked, root8Node64Step1Chunk6_4_checked, root8Node64Step1Chunk6_5_checked, root8Node64Step1Chunk7_0_checked, root8Node64Step1Chunk7_1_checked, root8Node64Step1Chunk7_2_checked, root8Node64Step1Chunk7_3_checked, root8Node64Step1Chunk7_4_checked, root8Node64Step1Chunk7_5_checked, root8Node64Step1Chunk8_0_checked, root8Node64Step1Chunk8_1_checked, root8Node64Step1Chunk8_2_checked, root8Node64Step1Chunk8_3_checked, root8Node64Step1Chunk8_4_checked, root8Node64Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node64Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,0)]
  | 1 => [(7,1)]
  | 2 => [(7,5)]
  | 3 => [(6,0)]
  | 4 => [(7,1)]
  | 5 => [(7,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(8,2)]
  | 9 => [(8,0)]
  | 10 => [(7,3)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(6,4)]
  | 17 => [(1,2)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(0,3)]
  | 25 => [(8,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,3)]
  | 34 => [(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4)]
  | 42 => [(6,3)]
  | 43 => [(5,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(3,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1)]
  | 49 => [(0,2)]
  | 50 => [(4,4)]
  | 51 => [(1,4)]
  | 52 => [(0,5)]
  | 53 => [(2,4)]
  | 54 => [(1,3)]
  | 55 => [(5,2)]
  | 56 => [(7,5)]
  | 57 => [(6,0)]
  | 58 => [(7,1)]
  | 59 => [(6,5)]
  | _ => [(0,4)]
def root8Node64Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4)]
  | 51 => some [(1,4)]
  | 52 => some [(0,5)]
  | 53 => some [(2,4)]
  | 54 => some [(1,3)]
  | 55 => some [(5,2)]
  | 56 => some [(7,5)]
  | 57 => some [(6,0)]
  | 58 => some [(7,1)]
  | 59 => some [(6,5)]
  | _ => some [(0,4)]
theorem root8Node64Domains2_fast_eq : root8Node64Domains2 = expandDomains root8Node64Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node64Domains2 v = expandDomains root8Node64Domains2Fast v from by decide) v
theorem root8Node64Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root8Node64Domains1 root8Node64Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node64Domains1 root8Node64Domains2
    root8Node64Domains1Fast root8Node64Domains2Fast
    root8Node64Domains1_fast_eq root8Node64Domains2_fast_eq (by decide)
theorem root8Node64Step2_checked :
    checkReplacement table46 root8Node64Domains1 root8Node64Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node64Step2Chunk0_0_checked, root8Node64Step2Chunk0_1_checked, root8Node64Step2Chunk0_2_checked, root8Node64Step2Chunk0_3_checked, root8Node64Step2Chunk0_4_checked, root8Node64Step2Chunk0_5_checked, root8Node64Step2Chunk1_0_checked, root8Node64Step2Chunk1_1_checked, root8Node64Step2Chunk1_2_checked, root8Node64Step2Chunk1_3_checked, root8Node64Step2Chunk1_4_checked, root8Node64Step2Chunk1_5_checked, root8Node64Step2Chunk2_0_checked, root8Node64Step2Chunk2_1_checked, root8Node64Step2Chunk2_2_checked, root8Node64Step2Chunk2_3_checked, root8Node64Step2Chunk2_4_checked, root8Node64Step2Chunk2_5_checked, root8Node64Step2Chunk3_0_checked, root8Node64Step2Chunk3_1_checked, root8Node64Step2Chunk3_2_checked, root8Node64Step2Chunk3_3_checked, root8Node64Step2Chunk3_4_checked, root8Node64Step2Chunk3_5_checked, root8Node64Step2Chunk4_0_checked, root8Node64Step2Chunk4_1_checked, root8Node64Step2Chunk4_2_checked, root8Node64Step2Chunk4_3_checked, root8Node64Step2Chunk4_4_checked, root8Node64Step2Chunk4_5_checked, root8Node64Step2Chunk5_0_checked, root8Node64Step2Chunk5_1_checked, root8Node64Step2Chunk5_2_checked, root8Node64Step2Chunk5_3_checked, root8Node64Step2Chunk5_4_checked, root8Node64Step2Chunk5_5_checked, root8Node64Step2Chunk6_0_checked, root8Node64Step2Chunk6_1_checked, root8Node64Step2Chunk6_2_checked, root8Node64Step2Chunk6_3_checked, root8Node64Step2Chunk6_4_checked, root8Node64Step2Chunk6_5_checked, root8Node64Step2Chunk7_0_checked, root8Node64Step2Chunk7_1_checked, root8Node64Step2Chunk7_2_checked, root8Node64Step2Chunk7_3_checked, root8Node64Step2Chunk7_4_checked, root8Node64Step2Chunk7_5_checked, root8Node64Step2Chunk8_0_checked, root8Node64Step2Chunk8_1_checked, root8Node64Step2Chunk8_2_checked, root8Node64Step2Chunk8_3_checked, root8Node64Step2Chunk8_4_checked, root8Node64Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node64Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node64Domains2 (.output 31) = true := by decide
def root8Node65Domains0 : Domains 61 State := restrict root8Node63Domains3 0 (6,0)
def root8Node65Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(7,5)]
  | 3 => some [(6,0)]
  | 4 => some [(7,1)]
  | 5 => some [(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(6,4)]
  | 17 => some [(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3)]
  | 25 => some [(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,3)]
  | 34 => some [(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4)]
  | 42 => some [(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1)]
  | 49 => some [(0,2)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(6,3)]
  | 53 => some [(2,2),(2,4)]
  | 54 => some [(1,3),(3,3)]
  | 55 => some [(5,2)]
  | 56 => some [(4,1),(7,5)]
  | 57 => some [(0,2),(6,0)]
  | 58 => some [(1,1),(7,1)]
  | 59 => some [(0,1),(6,5)]
  | _ => some [(0,4),(6,2)]
theorem root8Node65Domains0_fast_eq : root8Node65Domains0 = expandDomains root8Node65Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node65Domains0 v = expandDomains root8Node65Domains0Fast v from by decide) v
end SpectreFinite.HexSearch.RadiusFour
