module

public import SpectreFinite.RadiusFourRoot8Part18
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable14
public import SpectreFinite.RadiusFourTable31
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node60Domains0 : Domains 61 State := restrict root8Node56Domains1 10 (8,3)
def root8Node60Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node60Domains0_fast_eq : root8Node60Domains0 = expandDomains root8Node60Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node60Domains0 v = expandDomains root8Node60Domains0Fast v from by decide) v
def root8Node60Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(3,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(1,5)]
  | 50 => [(4,4),(7,2)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(1,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(6,5)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root8Node60Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node60Domains1_fast_eq : root8Node60Domains1 = expandDomains root8Node60Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node60Domains1 v = expandDomains root8Node60Domains1Fast v from by decide) v
theorem root8Node60Step1Chunk0_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk0_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk0_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk0_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk0_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk0_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk1_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk2_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk3_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk4_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk5_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk6_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk7_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_0⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_1⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_2⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_3⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_4⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1Chunk8_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_5⟩
      root8Node60Domains0 root8Node60Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains0 root8Node60Domains1
    root8Node60Domains0Fast root8Node60Domains1Fast
    root8Node60Domains0_fast_eq root8Node60Domains1_fast_eq (by decide)
theorem root8Node60Step1_checked :
    checkReplacement table31 root8Node60Domains0 root8Node60Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node60Step1Chunk0_0_checked, root8Node60Step1Chunk0_1_checked, root8Node60Step1Chunk0_2_checked, root8Node60Step1Chunk0_3_checked, root8Node60Step1Chunk0_4_checked, root8Node60Step1Chunk0_5_checked, root8Node60Step1Chunk1_0_checked, root8Node60Step1Chunk1_1_checked, root8Node60Step1Chunk1_2_checked, root8Node60Step1Chunk1_3_checked, root8Node60Step1Chunk1_4_checked, root8Node60Step1Chunk1_5_checked, root8Node60Step1Chunk2_0_checked, root8Node60Step1Chunk2_1_checked, root8Node60Step1Chunk2_2_checked, root8Node60Step1Chunk2_3_checked, root8Node60Step1Chunk2_4_checked, root8Node60Step1Chunk2_5_checked, root8Node60Step1Chunk3_0_checked, root8Node60Step1Chunk3_1_checked, root8Node60Step1Chunk3_2_checked, root8Node60Step1Chunk3_3_checked, root8Node60Step1Chunk3_4_checked, root8Node60Step1Chunk3_5_checked, root8Node60Step1Chunk4_0_checked, root8Node60Step1Chunk4_1_checked, root8Node60Step1Chunk4_2_checked, root8Node60Step1Chunk4_3_checked, root8Node60Step1Chunk4_4_checked, root8Node60Step1Chunk4_5_checked, root8Node60Step1Chunk5_0_checked, root8Node60Step1Chunk5_1_checked, root8Node60Step1Chunk5_2_checked, root8Node60Step1Chunk5_3_checked, root8Node60Step1Chunk5_4_checked, root8Node60Step1Chunk5_5_checked, root8Node60Step1Chunk6_0_checked, root8Node60Step1Chunk6_1_checked, root8Node60Step1Chunk6_2_checked, root8Node60Step1Chunk6_3_checked, root8Node60Step1Chunk6_4_checked, root8Node60Step1Chunk6_5_checked, root8Node60Step1Chunk7_0_checked, root8Node60Step1Chunk7_1_checked, root8Node60Step1Chunk7_2_checked, root8Node60Step1Chunk7_3_checked, root8Node60Step1Chunk7_4_checked, root8Node60Step1Chunk7_5_checked, root8Node60Step1Chunk8_0_checked, root8Node60Step1Chunk8_1_checked, root8Node60Step1Chunk8_2_checked, root8Node60Step1Chunk8_3_checked, root8Node60Step1Chunk8_4_checked, root8Node60Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node60Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(3,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(8,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(5,5),(8,5)]
  | 56 => [(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(1,4),(3,4)]
  | _ => [(0,5),(6,3)]
def root8Node60Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(5,5),(8,5)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(1,4),(3,4)]
  | _ => some [(0,5),(6,3)]
theorem root8Node60Domains2_fast_eq : root8Node60Domains2 = expandDomains root8Node60Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node60Domains2 v = expandDomains root8Node60Domains2Fast v from by decide) v
theorem root8Node60Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root8Node60Domains1 root8Node60Domains2 = true := by
  exact checkNarrowing_of_fast _ root8Node60Domains1 root8Node60Domains2
    root8Node60Domains1Fast root8Node60Domains2Fast
    root8Node60Domains1_fast_eq root8Node60Domains2_fast_eq (by decide)
theorem root8Node60Step2_checked :
    checkReplacement table46 root8Node60Domains1 root8Node60Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node60Step2Chunk0_0_checked, root8Node60Step2Chunk0_1_checked, root8Node60Step2Chunk0_2_checked, root8Node60Step2Chunk0_3_checked, root8Node60Step2Chunk0_4_checked, root8Node60Step2Chunk0_5_checked, root8Node60Step2Chunk1_0_checked, root8Node60Step2Chunk1_1_checked, root8Node60Step2Chunk1_2_checked, root8Node60Step2Chunk1_3_checked, root8Node60Step2Chunk1_4_checked, root8Node60Step2Chunk1_5_checked, root8Node60Step2Chunk2_0_checked, root8Node60Step2Chunk2_1_checked, root8Node60Step2Chunk2_2_checked, root8Node60Step2Chunk2_3_checked, root8Node60Step2Chunk2_4_checked, root8Node60Step2Chunk2_5_checked, root8Node60Step2Chunk3_0_checked, root8Node60Step2Chunk3_1_checked, root8Node60Step2Chunk3_2_checked, root8Node60Step2Chunk3_3_checked, root8Node60Step2Chunk3_4_checked, root8Node60Step2Chunk3_5_checked, root8Node60Step2Chunk4_0_checked, root8Node60Step2Chunk4_1_checked, root8Node60Step2Chunk4_2_checked, root8Node60Step2Chunk4_3_checked, root8Node60Step2Chunk4_4_checked, root8Node60Step2Chunk4_5_checked, root8Node60Step2Chunk5_0_checked, root8Node60Step2Chunk5_1_checked, root8Node60Step2Chunk5_2_checked, root8Node60Step2Chunk5_3_checked, root8Node60Step2Chunk5_4_checked, root8Node60Step2Chunk5_5_checked, root8Node60Step2Chunk6_0_checked, root8Node60Step2Chunk6_1_checked, root8Node60Step2Chunk6_2_checked, root8Node60Step2Chunk6_3_checked, root8Node60Step2Chunk6_4_checked, root8Node60Step2Chunk6_5_checked, root8Node60Step2Chunk7_0_checked, root8Node60Step2Chunk7_1_checked, root8Node60Step2Chunk7_2_checked, root8Node60Step2Chunk7_3_checked, root8Node60Step2Chunk7_4_checked, root8Node60Step2Chunk7_5_checked, root8Node60Step2Chunk8_0_checked, root8Node60Step2Chunk8_1_checked, root8Node60Step2Chunk8_2_checked, root8Node60Step2Chunk8_3_checked, root8Node60Step2Chunk8_4_checked, root8Node60Step2Chunk8_5_checked, Bool.true_and]
  · decide
def root8Node61Domains0 : Domains 61 State := restrict root8Node60Domains2 55 (5,5)
def root8Node61Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(5,5)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(1,4),(3,4)]
  | _ => some [(0,5),(6,3)]
theorem root8Node61Domains0_fast_eq : root8Node61Domains0 = expandDomains root8Node61Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node61Domains0 v = expandDomains root8Node61Domains0Fast v from by decide) v
def root8Node61Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(3,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(8,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(5,5)]
  | 56 => [(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(1,4)]
  | _ => [(0,5)]
def root8Node61Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(5,5)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(1,4)]
  | _ => some [(0,5)]
theorem root8Node61Domains1_fast_eq : root8Node61Domains1 = expandDomains root8Node61Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node61Domains1 v = expandDomains root8Node61Domains1Fast v from by decide) v
theorem root8Node61Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root8Node61Domains0 root8Node61Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node61Domains0 root8Node61Domains1
    root8Node61Domains0Fast root8Node61Domains1Fast
    root8Node61Domains0_fast_eq root8Node61Domains1_fast_eq (by decide)
theorem root8Node61Step1_checked :
    checkReplacement table39 root8Node61Domains0 root8Node61Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node61Step1Chunk0_0_checked, root8Node61Step1Chunk0_1_checked, root8Node61Step1Chunk0_2_checked, root8Node61Step1Chunk0_3_checked, root8Node61Step1Chunk0_4_checked, root8Node61Step1Chunk0_5_checked, root8Node61Step1Chunk1_0_checked, root8Node61Step1Chunk1_1_checked, root8Node61Step1Chunk1_2_checked, root8Node61Step1Chunk1_3_checked, root8Node61Step1Chunk1_4_checked, root8Node61Step1Chunk1_5_checked, root8Node61Step1Chunk2_0_checked, root8Node61Step1Chunk2_1_checked, root8Node61Step1Chunk2_2_checked, root8Node61Step1Chunk2_3_checked, root8Node61Step1Chunk2_4_checked, root8Node61Step1Chunk2_5_checked, root8Node61Step1Chunk3_0_checked, root8Node61Step1Chunk3_1_checked, root8Node61Step1Chunk3_2_checked, root8Node61Step1Chunk3_3_checked, root8Node61Step1Chunk3_4_checked, root8Node61Step1Chunk3_5_checked, root8Node61Step1Chunk4_0_checked, root8Node61Step1Chunk4_1_checked, root8Node61Step1Chunk4_2_checked, root8Node61Step1Chunk4_3_checked, root8Node61Step1Chunk4_4_checked, root8Node61Step1Chunk4_5_checked, root8Node61Step1Chunk5_0_checked, root8Node61Step1Chunk5_1_checked, root8Node61Step1Chunk5_2_checked, root8Node61Step1Chunk5_3_checked, root8Node61Step1Chunk5_4_checked, root8Node61Step1Chunk5_5_checked, root8Node61Step1Chunk6_0_checked, root8Node61Step1Chunk6_1_checked, root8Node61Step1Chunk6_2_checked, root8Node61Step1Chunk6_3_checked, root8Node61Step1Chunk6_4_checked, root8Node61Step1Chunk6_5_checked, root8Node61Step1Chunk7_0_checked, root8Node61Step1Chunk7_1_checked, root8Node61Step1Chunk7_2_checked, root8Node61Step1Chunk7_3_checked, root8Node61Step1Chunk7_4_checked, root8Node61Step1Chunk7_5_checked, root8Node61Step1Chunk8_0_checked, root8Node61Step1Chunk8_1_checked, root8Node61Step1Chunk8_2_checked, root8Node61Step1Chunk8_3_checked, root8Node61Step1Chunk8_4_checked, root8Node61Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node61Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node61Domains1 (.output 29) = true := by decide
def root8Node62Domains0 : Domains 61 State := restrict root8Node60Domains2 55 (8,5)
def root8Node62Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(1,4),(3,4)]
  | _ => some [(0,5),(6,3)]
theorem root8Node62Domains0_fast_eq : root8Node62Domains0 = expandDomains root8Node62Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node62Domains0 v = expandDomains root8Node62Domains0Fast v from by decide) v
def root8Node62Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(4,1)]
  | 3 => [(0,2)]
  | 4 => [(1,1)]
  | 5 => [(3,2)]
  | 6 => [(4,0)]
  | 7 => [(7,3)]
  | 8 => [(5,2)]
  | 9 => [(8,0)]
  | 10 => [(8,3)]
  | 11 => [(6,1)]
  | 12 => [(5,1)]
  | 13 => [(0,1)]
  | 14 => [(6,2)]
  | 15 => [(8,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(7,0)]
  | 19 => [(8,3)]
  | 20 => [(8,5)]
  | 21 => [(1,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(7,1)]
  | 26 => [(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(8,2)]
  | 33 => [(5,0)]
  | 34 => [(4,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(8,4)]
  | 42 => [(0,0)]
  | 43 => [(8,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(7,5)]
  | 47 => [(0,3)]
  | 48 => [(8,1)]
  | 49 => [(1,5)]
  | 50 => [(7,2)]
  | 51 => [(7,4)]
  | 52 => [(1,3)]
  | 53 => [(4,2)]
  | 54 => [(5,3)]
  | 55 => [(8,5)]
  | 56 => [(8,1)]
  | 57 => [(6,5)]
  | 58 => [(0,4)]
  | 59 => [(3,4)]
  | _ => [(6,3)]
def root8Node62Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(4,1)]
  | 3 => some [(0,2)]
  | 4 => some [(1,1)]
  | 5 => some [(3,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2)]
  | 9 => some [(8,0)]
  | 10 => some [(8,3)]
  | 11 => some [(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(7,1)]
  | 26 => some [(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(8,2)]
  | 33 => some [(5,0)]
  | 34 => some [(4,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(8,4)]
  | 42 => some [(0,0)]
  | 43 => some [(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(8,1)]
  | 49 => some [(1,5)]
  | 50 => some [(7,2)]
  | 51 => some [(7,4)]
  | 52 => some [(1,3)]
  | 53 => some [(4,2)]
  | 54 => some [(5,3)]
  | 55 => some [(8,5)]
  | 56 => some [(8,1)]
  | 57 => some [(6,5)]
  | 58 => some [(0,4)]
  | 59 => some [(3,4)]
  | _ => some [(6,3)]
theorem root8Node62Domains1_fast_eq : root8Node62Domains1 = expandDomains root8Node62Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node62Domains1 v = expandDomains root8Node62Domains1Fast v from by decide) v
theorem root8Node62Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root8Node62Domains0 root8Node62Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node62Domains0 root8Node62Domains1
    root8Node62Domains0Fast root8Node62Domains1Fast
    root8Node62Domains0_fast_eq root8Node62Domains1_fast_eq (by decide)
theorem root8Node62Step1_checked :
    checkReplacement table39 root8Node62Domains0 root8Node62Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node62Step1Chunk0_0_checked, root8Node62Step1Chunk0_1_checked, root8Node62Step1Chunk0_2_checked, root8Node62Step1Chunk0_3_checked, root8Node62Step1Chunk0_4_checked, root8Node62Step1Chunk0_5_checked, root8Node62Step1Chunk1_0_checked, root8Node62Step1Chunk1_1_checked, root8Node62Step1Chunk1_2_checked, root8Node62Step1Chunk1_3_checked, root8Node62Step1Chunk1_4_checked, root8Node62Step1Chunk1_5_checked, root8Node62Step1Chunk2_0_checked, root8Node62Step1Chunk2_1_checked, root8Node62Step1Chunk2_2_checked, root8Node62Step1Chunk2_3_checked, root8Node62Step1Chunk2_4_checked, root8Node62Step1Chunk2_5_checked, root8Node62Step1Chunk3_0_checked, root8Node62Step1Chunk3_1_checked, root8Node62Step1Chunk3_2_checked, root8Node62Step1Chunk3_3_checked, root8Node62Step1Chunk3_4_checked, root8Node62Step1Chunk3_5_checked, root8Node62Step1Chunk4_0_checked, root8Node62Step1Chunk4_1_checked, root8Node62Step1Chunk4_2_checked, root8Node62Step1Chunk4_3_checked, root8Node62Step1Chunk4_4_checked, root8Node62Step1Chunk4_5_checked, root8Node62Step1Chunk5_0_checked, root8Node62Step1Chunk5_1_checked, root8Node62Step1Chunk5_2_checked, root8Node62Step1Chunk5_3_checked, root8Node62Step1Chunk5_4_checked, root8Node62Step1Chunk5_5_checked, root8Node62Step1Chunk6_0_checked, root8Node62Step1Chunk6_1_checked, root8Node62Step1Chunk6_2_checked, root8Node62Step1Chunk6_3_checked, root8Node62Step1Chunk6_4_checked, root8Node62Step1Chunk6_5_checked, root8Node62Step1Chunk7_0_checked, root8Node62Step1Chunk7_1_checked, root8Node62Step1Chunk7_2_checked, root8Node62Step1Chunk7_3_checked, root8Node62Step1Chunk7_4_checked, root8Node62Step1Chunk7_5_checked, root8Node62Step1Chunk8_0_checked, root8Node62Step1Chunk8_1_checked, root8Node62Step1Chunk8_2_checked, root8Node62Step1Chunk8_3_checked, root8Node62Step1Chunk8_4_checked, root8Node62Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node62Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node62Domains1 (.output 30) = true := by decide
def root8Node63Domains0 : Domains 61 State := restrict root8Node47Domains3 1 (7,1)
def root8Node63Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2),(1,0),(6,0)]
  | 1 => some [(7,1)]
  | 2 => some [(4,1),(7,5)]
  | 3 => some [(0,2),(6,0)]
  | 4 => some [(1,1),(7,1)]
  | 5 => some [(1,2),(3,2),(7,2)]
  | 6 => some [(4,0)]
  | 7 => some [(7,3)]
  | 8 => some [(5,2),(8,2)]
  | 9 => some [(8,0)]
  | 10 => some [(7,3),(8,3)]
  | 11 => some [(0,3),(6,1)]
  | 12 => some [(5,1)]
  | 13 => some [(0,1)]
  | 14 => some [(6,2)]
  | 15 => some [(8,4)]
  | 16 => some [(1,4),(6,4)]
  | 17 => some [(0,5),(1,2)]
  | 18 => some [(4,2),(7,0)]
  | 19 => some [(5,3),(8,3)]
  | 20 => some [(8,5)]
  | 21 => some [(1,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(0,3),(6,0)]
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2),(8,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node63Domains0_fast_eq : root8Node63Domains0 = expandDomains root8Node63Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node63Domains0 v = expandDomains root8Node63Domains0Fast v from by decide) v
def root8Node63Domains1 (v : Fin 61) : List State :=
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
  | 25 => [(7,1),(8,1)]
  | 26 => [(1,2),(7,2)]
  | 27 => [(7,4)]
  | 28 => [(1,3)]
  | 29 => [(8,2)]
  | 30 => [(8,0)]
  | 31 => [(7,3)]
  | 32 => [(4,2)]
  | 33 => [(5,0),(5,3)]
  | 34 => [(4,5),(8,5)]
  | 35 => [(8,1)]
  | 36 => [(6,5)]
  | 37 => [(0,4)]
  | 38 => [(5,4)]
  | 39 => [(6,4)]
  | 40 => [(1,2)]
  | 41 => [(7,4),(8,4)]
  | 42 => [(0,0),(6,3)]
  | 43 => [(5,5),(8,5)]
  | 44 => [(7,0)]
  | 45 => [(4,3)]
  | 46 => [(3,5),(7,5)]
  | 47 => [(0,3)]
  | 48 => [(4,1),(8,1)]
  | 49 => [(0,2),(1,5)]
  | 50 => [(4,4),(7,2)]
  | 51 => [(1,4),(7,4)]
  | 52 => [(0,5),(1,3),(6,3)]
  | 53 => [(2,2),(2,4),(4,2)]
  | 54 => [(1,3),(3,3),(5,3)]
  | 55 => [(5,2),(5,5),(8,5)]
  | 56 => [(4,1),(7,5),(8,1)]
  | 57 => [(0,2),(6,0),(6,5)]
  | 58 => [(0,4),(1,1),(7,1)]
  | 59 => [(0,1),(1,4),(3,4),(6,5)]
  | _ => [(0,4),(0,5),(6,2),(6,3)]
def root8Node63Domains1Fast (v : Fin 61) : Option (List State) :=
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
  | 25 => some [(7,1),(8,1)]
  | 26 => some [(1,2),(7,2)]
  | 27 => some [(7,4)]
  | 28 => some [(1,3)]
  | 29 => some [(8,2)]
  | 30 => some [(8,0)]
  | 31 => some [(7,3)]
  | 32 => some [(4,2)]
  | 33 => some [(5,0),(5,3)]
  | 34 => some [(4,5),(8,5)]
  | 35 => some [(8,1)]
  | 36 => some [(6,5)]
  | 37 => some [(0,4)]
  | 38 => some [(5,4)]
  | 39 => some [(6,4)]
  | 40 => some [(1,2)]
  | 41 => some [(7,4),(8,4)]
  | 42 => some [(0,0),(6,3)]
  | 43 => some [(5,5),(8,5)]
  | 44 => some [(7,0)]
  | 45 => some [(4,3)]
  | 46 => some [(3,5),(7,5)]
  | 47 => some [(0,3)]
  | 48 => some [(4,1),(8,1)]
  | 49 => some [(0,2),(1,5)]
  | 50 => some [(4,4),(7,2)]
  | 51 => some [(1,4),(7,4)]
  | 52 => some [(0,5),(1,3),(6,3)]
  | 53 => some [(2,2),(2,4),(4,2)]
  | 54 => some [(1,3),(3,3),(5,3)]
  | 55 => some [(5,2),(5,5),(8,5)]
  | 56 => some [(4,1),(7,5),(8,1)]
  | 57 => some [(0,2),(6,0),(6,5)]
  | 58 => some [(0,4),(1,1),(7,1)]
  | 59 => some [(0,1),(1,4),(3,4),(6,5)]
  | _ => some [(0,4),(0,5),(6,2),(6,3)]
theorem root8Node63Domains1_fast_eq : root8Node63Domains1 = expandDomains root8Node63Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node63Domains1 v = expandDomains root8Node63Domains1Fast v from by decide) v
theorem root8Node63Step1Chunk0_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk0_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk0_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk0_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk0_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk0_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows0_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk1_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows1_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk2_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows2_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk3_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows3_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk4_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows4_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk5_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows5_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk6_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows6_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk7_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows7_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_0_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_0⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_1_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_1⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_2_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_2⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_3_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_3⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_4_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_4⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1Chunk8_5_checked :
    checkNarrowing ⟨table14Scope, table14Rows8_5⟩
      root8Node63Domains0 root8Node63Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node63Domains0 root8Node63Domains1
    root8Node63Domains0Fast root8Node63Domains1Fast
    root8Node63Domains0_fast_eq root8Node63Domains1_fast_eq (by decide)
theorem root8Node63Step1_checked :
    checkReplacement table14 root8Node63Domains0 root8Node63Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node63Step1Chunk0_0_checked, root8Node63Step1Chunk0_1_checked, root8Node63Step1Chunk0_2_checked, root8Node63Step1Chunk0_3_checked, root8Node63Step1Chunk0_4_checked, root8Node63Step1Chunk0_5_checked, root8Node63Step1Chunk1_0_checked, root8Node63Step1Chunk1_1_checked, root8Node63Step1Chunk1_2_checked, root8Node63Step1Chunk1_3_checked, root8Node63Step1Chunk1_4_checked, root8Node63Step1Chunk1_5_checked, root8Node63Step1Chunk2_0_checked, root8Node63Step1Chunk2_1_checked, root8Node63Step1Chunk2_2_checked, root8Node63Step1Chunk2_3_checked, root8Node63Step1Chunk2_4_checked, root8Node63Step1Chunk2_5_checked, root8Node63Step1Chunk3_0_checked, root8Node63Step1Chunk3_1_checked, root8Node63Step1Chunk3_2_checked, root8Node63Step1Chunk3_3_checked, root8Node63Step1Chunk3_4_checked, root8Node63Step1Chunk3_5_checked, root8Node63Step1Chunk4_0_checked, root8Node63Step1Chunk4_1_checked, root8Node63Step1Chunk4_2_checked, root8Node63Step1Chunk4_3_checked, root8Node63Step1Chunk4_4_checked, root8Node63Step1Chunk4_5_checked, root8Node63Step1Chunk5_0_checked, root8Node63Step1Chunk5_1_checked, root8Node63Step1Chunk5_2_checked, root8Node63Step1Chunk5_3_checked, root8Node63Step1Chunk5_4_checked, root8Node63Step1Chunk5_5_checked, root8Node63Step1Chunk6_0_checked, root8Node63Step1Chunk6_1_checked, root8Node63Step1Chunk6_2_checked, root8Node63Step1Chunk6_3_checked, root8Node63Step1Chunk6_4_checked, root8Node63Step1Chunk6_5_checked, root8Node63Step1Chunk7_0_checked, root8Node63Step1Chunk7_1_checked, root8Node63Step1Chunk7_2_checked, root8Node63Step1Chunk7_3_checked, root8Node63Step1Chunk7_4_checked, root8Node63Step1Chunk7_5_checked, root8Node63Step1Chunk8_0_checked, root8Node63Step1Chunk8_1_checked, root8Node63Step1Chunk8_2_checked, root8Node63Step1Chunk8_3_checked, root8Node63Step1Chunk8_4_checked, root8Node63Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
