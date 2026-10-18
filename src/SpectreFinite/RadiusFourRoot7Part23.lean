module

public import SpectreFinite.RadiusFourRoot7Part22
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable2
public import SpectreFinite.RadiusFourTable37
public import SpectreFinite.RadiusFourTable38
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root7Node70Domains0 : Domains 61 State := restrict root7Node64Domains2 35 (6,2)
def root7Node70Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(8,3)]
  | 6 => some [(5,5)]
  | 7 => some [(1,0)]
  | 8 => some [(2,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(3,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(4,5),(5,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5),(8,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(4,4),(7,2)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(4,4),(7,2)]
  | _ => some [(1,4),(7,4)]
theorem root7Node70Domains0_fast_eq : root7Node70Domains0 = expandDomains root7Node70Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node70Domains0 v = expandDomains root7Node70Domains0Fast v from by decide) v
def root7Node70Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,1)]
  | 1 => [(0,1)]
  | 2 => [(6,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(8,3)]
  | 6 => [(5,5)]
  | 7 => [(1,0)]
  | 8 => [(2,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(3,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(7,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(8,2)]
  | 42 => [(5,0),(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(7,0)]
  | 55 => [(4,3)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(6,3)]
  | 59 => [(7,2)]
  | _ => [(1,4),(7,4)]
def root7Node70Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(8,3)]
  | 6 => some [(5,5)]
  | 7 => some [(1,0)]
  | 8 => some [(2,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(3,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(5,0),(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(6,3)]
  | 59 => some [(7,2)]
  | _ => some [(1,4),(7,4)]
theorem root7Node70Domains1_fast_eq : root7Node70Domains1 = expandDomains root7Node70Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node70Domains1 v = expandDomains root7Node70Domains1Fast v from by decide) v
theorem root7Node70Step1Chunk0_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_0⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk0_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_1⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk0_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_2⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk0_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_3⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk0_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_4⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk0_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows0_5⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk1_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_0⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk1_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_1⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk1_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_2⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk1_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_3⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk1_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_4⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk1_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows1_5⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk2_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_0⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk2_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_1⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk2_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_2⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk2_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_3⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk2_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_4⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk2_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows2_5⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk3_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_0⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk3_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_1⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk3_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_2⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk3_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_3⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk3_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_4⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk3_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows3_5⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk4_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_0⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk4_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_1⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk4_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_2⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk4_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_3⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk4_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_4⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk4_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows4_5⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk5_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_0⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk5_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_1⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk5_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_2⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk5_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_3⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk5_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_4⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk5_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows5_5⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk6_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_0⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk6_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_1⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk6_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_2⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk6_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_3⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk6_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_4⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk6_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows6_5⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk7_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_0⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk7_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_1⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk7_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_2⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk7_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_3⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk7_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_4⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk7_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows7_5⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk8_0_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_0⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk8_1_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_1⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk8_2_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_2⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk8_3_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_3⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk8_4_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_4⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1Chunk8_5_checked :
    checkNarrowing ⟨table38Scope, table38Rows8_5⟩
      root7Node70Domains0 root7Node70Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains0 root7Node70Domains1
    root7Node70Domains0Fast root7Node70Domains1Fast
    root7Node70Domains0_fast_eq root7Node70Domains1_fast_eq (by decide)
theorem root7Node70Step1_checked :
    checkReplacement table38 root7Node70Domains0 root7Node70Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node70Step1Chunk0_0_checked, root7Node70Step1Chunk0_1_checked, root7Node70Step1Chunk0_2_checked, root7Node70Step1Chunk0_3_checked, root7Node70Step1Chunk0_4_checked, root7Node70Step1Chunk0_5_checked, root7Node70Step1Chunk1_0_checked, root7Node70Step1Chunk1_1_checked, root7Node70Step1Chunk1_2_checked, root7Node70Step1Chunk1_3_checked, root7Node70Step1Chunk1_4_checked, root7Node70Step1Chunk1_5_checked, root7Node70Step1Chunk2_0_checked, root7Node70Step1Chunk2_1_checked, root7Node70Step1Chunk2_2_checked, root7Node70Step1Chunk2_3_checked, root7Node70Step1Chunk2_4_checked, root7Node70Step1Chunk2_5_checked, root7Node70Step1Chunk3_0_checked, root7Node70Step1Chunk3_1_checked, root7Node70Step1Chunk3_2_checked, root7Node70Step1Chunk3_3_checked, root7Node70Step1Chunk3_4_checked, root7Node70Step1Chunk3_5_checked, root7Node70Step1Chunk4_0_checked, root7Node70Step1Chunk4_1_checked, root7Node70Step1Chunk4_2_checked, root7Node70Step1Chunk4_3_checked, root7Node70Step1Chunk4_4_checked, root7Node70Step1Chunk4_5_checked, root7Node70Step1Chunk5_0_checked, root7Node70Step1Chunk5_1_checked, root7Node70Step1Chunk5_2_checked, root7Node70Step1Chunk5_3_checked, root7Node70Step1Chunk5_4_checked, root7Node70Step1Chunk5_5_checked, root7Node70Step1Chunk6_0_checked, root7Node70Step1Chunk6_1_checked, root7Node70Step1Chunk6_2_checked, root7Node70Step1Chunk6_3_checked, root7Node70Step1Chunk6_4_checked, root7Node70Step1Chunk6_5_checked, root7Node70Step1Chunk7_0_checked, root7Node70Step1Chunk7_1_checked, root7Node70Step1Chunk7_2_checked, root7Node70Step1Chunk7_3_checked, root7Node70Step1Chunk7_4_checked, root7Node70Step1Chunk7_5_checked, root7Node70Step1Chunk8_0_checked, root7Node70Step1Chunk8_1_checked, root7Node70Step1Chunk8_2_checked, root7Node70Step1Chunk8_3_checked, root7Node70Step1Chunk8_4_checked, root7Node70Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node70Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(5,1)]
  | 1 => [(0,1)]
  | 2 => [(6,2)]
  | 3 => [(7,4)]
  | 4 => [(6,3)]
  | 5 => [(8,3)]
  | 6 => [(5,5)]
  | 7 => [(1,0)]
  | 8 => [(2,1)]
  | 9 => [(0,2)]
  | 10 => [(1,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(3,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(7,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(8,2)]
  | 42 => [(8,0)]
  | 43 => [(7,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4)]
  | 49 => [(5,4)]
  | 50 => [(4,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(8,5)]
  | 54 => [(7,0)]
  | 55 => [(4,3)]
  | 56 => [(7,2)]
  | 57 => [(7,4)]
  | 58 => [(6,3)]
  | 59 => [(7,2)]
  | _ => [(7,4)]
def root7Node70Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(5,1)]
  | 1 => some [(0,1)]
  | 2 => some [(6,2)]
  | 3 => some [(7,4)]
  | 4 => some [(6,3)]
  | 5 => some [(8,3)]
  | 6 => some [(5,5)]
  | 7 => some [(1,0)]
  | 8 => some [(2,1)]
  | 9 => some [(0,2)]
  | 10 => some [(1,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(3,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(8,2)]
  | 42 => some [(8,0)]
  | 43 => some [(7,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4)]
  | 49 => some [(5,4)]
  | 50 => some [(4,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(8,5)]
  | 54 => some [(7,0)]
  | 55 => some [(4,3)]
  | 56 => some [(7,2)]
  | 57 => some [(7,4)]
  | 58 => some [(6,3)]
  | 59 => some [(7,2)]
  | _ => some [(7,4)]
theorem root7Node70Domains2_fast_eq : root7Node70Domains2 = expandDomains root7Node70Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node70Domains2 v = expandDomains root7Node70Domains2Fast v from by decide) v
theorem root7Node70Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node70Domains1 root7Node70Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node70Domains1 root7Node70Domains2
    root7Node70Domains1Fast root7Node70Domains2Fast
    root7Node70Domains1_fast_eq root7Node70Domains2_fast_eq (by decide)
theorem root7Node70Step2_checked :
    checkReplacement table39 root7Node70Domains1 root7Node70Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node70Step2Chunk0_0_checked, root7Node70Step2Chunk0_1_checked, root7Node70Step2Chunk0_2_checked, root7Node70Step2Chunk0_3_checked, root7Node70Step2Chunk0_4_checked, root7Node70Step2Chunk0_5_checked, root7Node70Step2Chunk1_0_checked, root7Node70Step2Chunk1_1_checked, root7Node70Step2Chunk1_2_checked, root7Node70Step2Chunk1_3_checked, root7Node70Step2Chunk1_4_checked, root7Node70Step2Chunk1_5_checked, root7Node70Step2Chunk2_0_checked, root7Node70Step2Chunk2_1_checked, root7Node70Step2Chunk2_2_checked, root7Node70Step2Chunk2_3_checked, root7Node70Step2Chunk2_4_checked, root7Node70Step2Chunk2_5_checked, root7Node70Step2Chunk3_0_checked, root7Node70Step2Chunk3_1_checked, root7Node70Step2Chunk3_2_checked, root7Node70Step2Chunk3_3_checked, root7Node70Step2Chunk3_4_checked, root7Node70Step2Chunk3_5_checked, root7Node70Step2Chunk4_0_checked, root7Node70Step2Chunk4_1_checked, root7Node70Step2Chunk4_2_checked, root7Node70Step2Chunk4_3_checked, root7Node70Step2Chunk4_4_checked, root7Node70Step2Chunk4_5_checked, root7Node70Step2Chunk5_0_checked, root7Node70Step2Chunk5_1_checked, root7Node70Step2Chunk5_2_checked, root7Node70Step2Chunk5_3_checked, root7Node70Step2Chunk5_4_checked, root7Node70Step2Chunk5_5_checked, root7Node70Step2Chunk6_0_checked, root7Node70Step2Chunk6_1_checked, root7Node70Step2Chunk6_2_checked, root7Node70Step2Chunk6_3_checked, root7Node70Step2Chunk6_4_checked, root7Node70Step2Chunk6_5_checked, root7Node70Step2Chunk7_0_checked, root7Node70Step2Chunk7_1_checked, root7Node70Step2Chunk7_2_checked, root7Node70Step2Chunk7_3_checked, root7Node70Step2Chunk7_4_checked, root7Node70Step2Chunk7_5_checked, root7Node70Step2Chunk8_0_checked, root7Node70Step2Chunk8_1_checked, root7Node70Step2Chunk8_2_checked, root7Node70Step2Chunk8_3_checked, root7Node70Step2Chunk8_4_checked, root7Node70Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node70Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node70Domains2 (.output 34) = true := by decide
def root7Node71Domains0 : Domains 61 State := restrict root7Node61Domains3 0 (8,1)
def root7Node71Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,1)]
  | 1 => some [(0,1),(6,5)]
  | 2 => some [(0,4),(6,2)]
  | 3 => some [(1,4),(7,4)]
  | 4 => some [(0,5),(6,3)]
  | 5 => some [(8,3)]
  | 6 => some [(5,5)]
  | 7 => some [(1,0),(3,0)]
  | 8 => some [(2,1),(2,5)]
  | 9 => some [(0,2),(6,0)]
  | 10 => some [(1,1),(7,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(3,2),(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3),(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,4),(1,2),(6,2)]
  | 36 => some [(5,4),(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(6,3)]
  | 41 => some [(7,2),(8,2)]
  | 42 => some [(4,0),(5,0),(8,0)]
  | 43 => some [(4,3),(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(4,1),(8,1)]
  | 47 => some [(0,2),(6,5)]
  | 48 => some [(0,4),(1,1)]
  | 49 => some [(5,1),(5,4)]
  | 50 => some [(0,5),(4,5),(5,5),(8,5)]
  | 51 => some [(2,0),(7,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,5)]
  | 54 => some [(7,0),(8,0)]
  | 55 => some [(4,3),(8,3)]
  | 56 => some [(3,1),(4,4),(7,2)]
  | 57 => some [(0,1),(1,4),(7,4)]
  | 58 => some [(0,5),(6,2),(6,3)]
  | 59 => some [(4,4),(7,2),(8,4)]
  | _ => some [(1,4),(7,4)]
theorem root7Node71Domains0_fast_eq : root7Node71Domains0 = expandDomains root7Node71Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node71Domains0 v = expandDomains root7Node71Domains0Fast v from by decide) v
def root7Node71Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,1)]
  | 1 => [(6,5)]
  | 2 => [(0,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(8,3)]
  | 6 => [(5,5)]
  | 7 => [(3,0)]
  | 8 => [(2,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(7,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(1,3),(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(0,4),(1,2),(6,2)]
  | 36 => [(5,4),(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3),(6,3)]
  | 41 => [(7,2),(8,2)]
  | 42 => [(4,0),(5,0),(8,0)]
  | 43 => [(4,3),(7,1),(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(4,1),(8,1)]
  | 47 => [(0,2),(6,5)]
  | 48 => [(0,4),(1,1)]
  | 49 => [(5,1),(5,4)]
  | 50 => [(0,5),(4,5),(5,5),(8,5)]
  | 51 => [(2,0),(7,0)]
  | 52 => [(7,3),(8,3)]
  | 53 => [(5,2),(5,5),(8,5)]
  | 54 => [(7,0),(8,0)]
  | 55 => [(4,3),(8,3)]
  | 56 => [(3,1),(4,4),(7,2)]
  | 57 => [(0,1),(1,4),(7,4)]
  | 58 => [(0,5),(6,2),(6,3)]
  | 59 => [(4,4),(7,2),(8,4)]
  | _ => [(1,4),(7,4)]
def root7Node71Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,1)]
  | 1 => some [(6,5)]
  | 2 => some [(0,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(8,3)]
  | 6 => some [(5,5)]
  | 7 => some [(3,0)]
  | 8 => some [(2,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3),(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,4),(1,2),(6,2)]
  | 36 => some [(5,4),(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(6,3)]
  | 41 => some [(7,2),(8,2)]
  | 42 => some [(4,0),(5,0),(8,0)]
  | 43 => some [(4,3),(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(4,1),(8,1)]
  | 47 => some [(0,2),(6,5)]
  | 48 => some [(0,4),(1,1)]
  | 49 => some [(5,1),(5,4)]
  | 50 => some [(0,5),(4,5),(5,5),(8,5)]
  | 51 => some [(2,0),(7,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,5)]
  | 54 => some [(7,0),(8,0)]
  | 55 => some [(4,3),(8,3)]
  | 56 => some [(3,1),(4,4),(7,2)]
  | 57 => some [(0,1),(1,4),(7,4)]
  | 58 => some [(0,5),(6,2),(6,3)]
  | 59 => some [(4,4),(7,2),(8,4)]
  | _ => some [(1,4),(7,4)]
theorem root7Node71Domains1_fast_eq : root7Node71Domains1 = expandDomains root7Node71Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node71Domains1 v = expandDomains root7Node71Domains1Fast v from by decide) v
theorem root7Node71Step1Chunk0_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_0⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk0_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_1⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk0_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_2⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk0_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_3⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk0_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_4⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk0_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows0_5⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk1_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_0⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk1_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_1⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk1_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_2⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk1_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_3⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk1_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_4⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk1_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows1_5⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk2_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_0⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk2_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_1⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk2_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_2⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk2_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_3⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk2_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_4⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk2_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows2_5⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk3_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_0⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk3_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_1⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk3_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_2⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk3_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_3⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk3_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_4⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk3_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows3_5⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk4_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_0⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk4_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_1⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk4_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_2⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk4_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_3⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk4_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_4⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk4_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows4_5⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk5_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_0⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk5_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_1⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk5_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_2⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk5_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_3⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk5_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_4⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk5_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows5_5⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk6_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_0⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk6_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_1⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk6_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_2⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk6_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_3⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk6_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_4⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk6_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows6_5⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk7_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_0⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk7_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_1⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk7_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_2⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk7_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_3⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk7_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_4⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk7_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows7_5⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk8_0_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_0⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk8_1_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_1⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk8_2_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_2⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk8_3_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_3⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk8_4_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_4⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1Chunk8_5_checked :
    checkNarrowing ⟨table2Scope, table2Rows8_5⟩
      root7Node71Domains0 root7Node71Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node71Domains0 root7Node71Domains1
    root7Node71Domains0Fast root7Node71Domains1Fast
    root7Node71Domains0_fast_eq root7Node71Domains1_fast_eq (by decide)
theorem root7Node71Step1_checked :
    checkReplacement table2 root7Node71Domains0 root7Node71Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node71Step1Chunk0_0_checked, root7Node71Step1Chunk0_1_checked, root7Node71Step1Chunk0_2_checked, root7Node71Step1Chunk0_3_checked, root7Node71Step1Chunk0_4_checked, root7Node71Step1Chunk0_5_checked, root7Node71Step1Chunk1_0_checked, root7Node71Step1Chunk1_1_checked, root7Node71Step1Chunk1_2_checked, root7Node71Step1Chunk1_3_checked, root7Node71Step1Chunk1_4_checked, root7Node71Step1Chunk1_5_checked, root7Node71Step1Chunk2_0_checked, root7Node71Step1Chunk2_1_checked, root7Node71Step1Chunk2_2_checked, root7Node71Step1Chunk2_3_checked, root7Node71Step1Chunk2_4_checked, root7Node71Step1Chunk2_5_checked, root7Node71Step1Chunk3_0_checked, root7Node71Step1Chunk3_1_checked, root7Node71Step1Chunk3_2_checked, root7Node71Step1Chunk3_3_checked, root7Node71Step1Chunk3_4_checked, root7Node71Step1Chunk3_5_checked, root7Node71Step1Chunk4_0_checked, root7Node71Step1Chunk4_1_checked, root7Node71Step1Chunk4_2_checked, root7Node71Step1Chunk4_3_checked, root7Node71Step1Chunk4_4_checked, root7Node71Step1Chunk4_5_checked, root7Node71Step1Chunk5_0_checked, root7Node71Step1Chunk5_1_checked, root7Node71Step1Chunk5_2_checked, root7Node71Step1Chunk5_3_checked, root7Node71Step1Chunk5_4_checked, root7Node71Step1Chunk5_5_checked, root7Node71Step1Chunk6_0_checked, root7Node71Step1Chunk6_1_checked, root7Node71Step1Chunk6_2_checked, root7Node71Step1Chunk6_3_checked, root7Node71Step1Chunk6_4_checked, root7Node71Step1Chunk6_5_checked, root7Node71Step1Chunk7_0_checked, root7Node71Step1Chunk7_1_checked, root7Node71Step1Chunk7_2_checked, root7Node71Step1Chunk7_3_checked, root7Node71Step1Chunk7_4_checked, root7Node71Step1Chunk7_5_checked, root7Node71Step1Chunk8_0_checked, root7Node71Step1Chunk8_1_checked, root7Node71Step1Chunk8_2_checked, root7Node71Step1Chunk8_3_checked, root7Node71Step1Chunk8_4_checked, root7Node71Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node72Domains0 : Domains 61 State := restrict root7Node71Domains1 26 (1,3)
def root7Node72Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,1)]
  | 1 => some [(6,5)]
  | 2 => some [(0,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(8,3)]
  | 6 => some [(5,5)]
  | 7 => some [(3,0)]
  | 8 => some [(2,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,4),(1,2),(6,2)]
  | 36 => some [(5,4),(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3),(6,3)]
  | 41 => some [(7,2),(8,2)]
  | 42 => some [(4,0),(5,0),(8,0)]
  | 43 => some [(4,3),(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(4,1),(8,1)]
  | 47 => some [(0,2),(6,5)]
  | 48 => some [(0,4),(1,1)]
  | 49 => some [(5,1),(5,4)]
  | 50 => some [(0,5),(4,5),(5,5),(8,5)]
  | 51 => some [(2,0),(7,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(5,2),(5,5),(8,5)]
  | 54 => some [(7,0),(8,0)]
  | 55 => some [(4,3),(8,3)]
  | 56 => some [(3,1),(4,4),(7,2)]
  | 57 => some [(0,1),(1,4),(7,4)]
  | 58 => some [(0,5),(6,2),(6,3)]
  | 59 => some [(4,4),(7,2),(8,4)]
  | _ => some [(1,4),(7,4)]
theorem root7Node72Domains0_fast_eq : root7Node72Domains0 = expandDomains root7Node72Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node72Domains0 v = expandDomains root7Node72Domains0Fast v from by decide) v
def root7Node72Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,1)]
  | 1 => [(6,5)]
  | 2 => [(0,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(8,3)]
  | 6 => [(5,5)]
  | 7 => [(3,0)]
  | 8 => [(2,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(7,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(1,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(7,2),(8,2)]
  | 42 => [(4,0),(5,0),(8,0)]
  | 43 => [(4,3)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(0,4),(1,1)]
  | 49 => [(5,1),(5,4)]
  | 50 => [(0,5)]
  | 51 => [(2,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(7,0),(8,0)]
  | 55 => [(4,3),(8,3)]
  | 56 => [(3,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(4,4),(7,2),(8,4)]
  | _ => [(1,4),(7,4)]
def root7Node72Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,1)]
  | 1 => some [(6,5)]
  | 2 => some [(0,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(8,3)]
  | 6 => some [(5,5)]
  | 7 => some [(3,0)]
  | 8 => some [(2,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2),(8,2)]
  | 42 => some [(4,0),(5,0),(8,0)]
  | 43 => some [(4,3)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(0,4),(1,1)]
  | 49 => some [(5,1),(5,4)]
  | 50 => some [(0,5)]
  | 51 => some [(2,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(7,0),(8,0)]
  | 55 => some [(4,3),(8,3)]
  | 56 => some [(3,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(4,4),(7,2),(8,4)]
  | _ => some [(1,4),(7,4)]
theorem root7Node72Domains1_fast_eq : root7Node72Domains1 = expandDomains root7Node72Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node72Domains1 v = expandDomains root7Node72Domains1Fast v from by decide) v
theorem root7Node72Step1Chunk0_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_0⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk0_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_1⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk0_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_2⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk0_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_3⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk0_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_4⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk0_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows0_5⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk1_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_0⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk1_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_1⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk1_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_2⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk1_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_3⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk1_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_4⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk1_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows1_5⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk2_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_0⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk2_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_1⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk2_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_2⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk2_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_3⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk2_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_4⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk2_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows2_5⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk3_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_0⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk3_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_1⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk3_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_2⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk3_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_3⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk3_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_4⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk3_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows3_5⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk4_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_0⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk4_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_1⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk4_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_2⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk4_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_3⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk4_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_4⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk4_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows4_5⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk5_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_0⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk5_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_1⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk5_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_2⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk5_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_3⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk5_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_4⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk5_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows5_5⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk6_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_0⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk6_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_1⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk6_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_2⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk6_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_3⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk6_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_4⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk6_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows6_5⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk7_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_0⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk7_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_1⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk7_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_2⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk7_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_3⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk7_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_4⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk7_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows7_5⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk8_0_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_0⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk8_1_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_1⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk8_2_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_2⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk8_3_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_3⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk8_4_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_4⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1Chunk8_5_checked :
    checkNarrowing ⟨table37Scope, table37Rows8_5⟩
      root7Node72Domains0 root7Node72Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains0 root7Node72Domains1
    root7Node72Domains0Fast root7Node72Domains1Fast
    root7Node72Domains0_fast_eq root7Node72Domains1_fast_eq (by decide)
theorem root7Node72Step1_checked :
    checkReplacement table37 root7Node72Domains0 root7Node72Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node72Step1Chunk0_0_checked, root7Node72Step1Chunk0_1_checked, root7Node72Step1Chunk0_2_checked, root7Node72Step1Chunk0_3_checked, root7Node72Step1Chunk0_4_checked, root7Node72Step1Chunk0_5_checked, root7Node72Step1Chunk1_0_checked, root7Node72Step1Chunk1_1_checked, root7Node72Step1Chunk1_2_checked, root7Node72Step1Chunk1_3_checked, root7Node72Step1Chunk1_4_checked, root7Node72Step1Chunk1_5_checked, root7Node72Step1Chunk2_0_checked, root7Node72Step1Chunk2_1_checked, root7Node72Step1Chunk2_2_checked, root7Node72Step1Chunk2_3_checked, root7Node72Step1Chunk2_4_checked, root7Node72Step1Chunk2_5_checked, root7Node72Step1Chunk3_0_checked, root7Node72Step1Chunk3_1_checked, root7Node72Step1Chunk3_2_checked, root7Node72Step1Chunk3_3_checked, root7Node72Step1Chunk3_4_checked, root7Node72Step1Chunk3_5_checked, root7Node72Step1Chunk4_0_checked, root7Node72Step1Chunk4_1_checked, root7Node72Step1Chunk4_2_checked, root7Node72Step1Chunk4_3_checked, root7Node72Step1Chunk4_4_checked, root7Node72Step1Chunk4_5_checked, root7Node72Step1Chunk5_0_checked, root7Node72Step1Chunk5_1_checked, root7Node72Step1Chunk5_2_checked, root7Node72Step1Chunk5_3_checked, root7Node72Step1Chunk5_4_checked, root7Node72Step1Chunk5_5_checked, root7Node72Step1Chunk6_0_checked, root7Node72Step1Chunk6_1_checked, root7Node72Step1Chunk6_2_checked, root7Node72Step1Chunk6_3_checked, root7Node72Step1Chunk6_4_checked, root7Node72Step1Chunk6_5_checked, root7Node72Step1Chunk7_0_checked, root7Node72Step1Chunk7_1_checked, root7Node72Step1Chunk7_2_checked, root7Node72Step1Chunk7_3_checked, root7Node72Step1Chunk7_4_checked, root7Node72Step1Chunk7_5_checked, root7Node72Step1Chunk8_0_checked, root7Node72Step1Chunk8_1_checked, root7Node72Step1Chunk8_2_checked, root7Node72Step1Chunk8_3_checked, root7Node72Step1Chunk8_4_checked, root7Node72Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node72Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(8,1)]
  | 1 => [(6,5)]
  | 2 => [(0,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(8,3)]
  | 6 => [(5,5)]
  | 7 => [(3,0)]
  | 8 => [(2,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(4,4)]
  | 14 => [(0,0)]
  | 15 => [(7,2)]
  | 16 => [(4,0)]
  | 17 => [(7,3)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(7,1)]
  | 21 => [(1,5)]
  | 22 => [(6,1)]
  | 23 => [(5,1)]
  | 24 => [(0,1)]
  | 25 => [(6,2)]
  | 26 => [(1,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(8,3)]
  | 32 => [(8,5)]
  | 33 => [(1,0)]
  | 34 => [(7,1)]
  | 35 => [(0,4)]
  | 36 => [(5,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(6,3)]
  | 41 => [(7,2)]
  | 42 => [(4,0)]
  | 43 => [(4,3)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(4,1)]
  | 47 => [(0,2)]
  | 48 => [(1,1)]
  | 49 => [(5,1)]
  | 50 => [(0,5)]
  | 51 => [(2,0)]
  | 52 => [(7,3)]
  | 53 => [(5,2)]
  | 54 => [(8,0)]
  | 55 => [(8,3)]
  | 56 => [(3,1)]
  | 57 => [(0,1)]
  | 58 => [(6,2)]
  | 59 => [(8,4)]
  | _ => [(1,4)]
def root7Node72Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(8,1)]
  | 1 => some [(6,5)]
  | 2 => some [(0,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(8,3)]
  | 6 => some [(5,5)]
  | 7 => some [(3,0)]
  | 8 => some [(2,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(4,4)]
  | 14 => some [(0,0)]
  | 15 => some [(7,2)]
  | 16 => some [(4,0)]
  | 17 => some [(7,3)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(1,5)]
  | 22 => some [(6,1)]
  | 23 => some [(5,1)]
  | 24 => some [(0,1)]
  | 25 => some [(6,2)]
  | 26 => some [(1,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(1,0)]
  | 34 => some [(7,1)]
  | 35 => some [(0,4)]
  | 36 => some [(5,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(6,3)]
  | 41 => some [(7,2)]
  | 42 => some [(4,0)]
  | 43 => some [(4,3)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(4,1)]
  | 47 => some [(0,2)]
  | 48 => some [(1,1)]
  | 49 => some [(5,1)]
  | 50 => some [(0,5)]
  | 51 => some [(2,0)]
  | 52 => some [(7,3)]
  | 53 => some [(5,2)]
  | 54 => some [(8,0)]
  | 55 => some [(8,3)]
  | 56 => some [(3,1)]
  | 57 => some [(0,1)]
  | 58 => some [(6,2)]
  | 59 => some [(8,4)]
  | _ => some [(1,4)]
theorem root7Node72Domains2_fast_eq : root7Node72Domains2 = expandDomains root7Node72Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node72Domains2 v = expandDomains root7Node72Domains2Fast v from by decide) v
theorem root7Node72Step2Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root7Node72Domains1 root7Node72Domains2 = true := by
  exact checkNarrowing_of_fast _ root7Node72Domains1 root7Node72Domains2
    root7Node72Domains1Fast root7Node72Domains2Fast
    root7Node72Domains1_fast_eq root7Node72Domains2_fast_eq (by decide)
theorem root7Node72Step2_checked :
    checkReplacement table39 root7Node72Domains1 root7Node72Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node72Step2Chunk0_0_checked, root7Node72Step2Chunk0_1_checked, root7Node72Step2Chunk0_2_checked, root7Node72Step2Chunk0_3_checked, root7Node72Step2Chunk0_4_checked, root7Node72Step2Chunk0_5_checked, root7Node72Step2Chunk1_0_checked, root7Node72Step2Chunk1_1_checked, root7Node72Step2Chunk1_2_checked, root7Node72Step2Chunk1_3_checked, root7Node72Step2Chunk1_4_checked, root7Node72Step2Chunk1_5_checked, root7Node72Step2Chunk2_0_checked, root7Node72Step2Chunk2_1_checked, root7Node72Step2Chunk2_2_checked, root7Node72Step2Chunk2_3_checked, root7Node72Step2Chunk2_4_checked, root7Node72Step2Chunk2_5_checked, root7Node72Step2Chunk3_0_checked, root7Node72Step2Chunk3_1_checked, root7Node72Step2Chunk3_2_checked, root7Node72Step2Chunk3_3_checked, root7Node72Step2Chunk3_4_checked, root7Node72Step2Chunk3_5_checked, root7Node72Step2Chunk4_0_checked, root7Node72Step2Chunk4_1_checked, root7Node72Step2Chunk4_2_checked, root7Node72Step2Chunk4_3_checked, root7Node72Step2Chunk4_4_checked, root7Node72Step2Chunk4_5_checked, root7Node72Step2Chunk5_0_checked, root7Node72Step2Chunk5_1_checked, root7Node72Step2Chunk5_2_checked, root7Node72Step2Chunk5_3_checked, root7Node72Step2Chunk5_4_checked, root7Node72Step2Chunk5_5_checked, root7Node72Step2Chunk6_0_checked, root7Node72Step2Chunk6_1_checked, root7Node72Step2Chunk6_2_checked, root7Node72Step2Chunk6_3_checked, root7Node72Step2Chunk6_4_checked, root7Node72Step2Chunk6_5_checked, root7Node72Step2Chunk7_0_checked, root7Node72Step2Chunk7_1_checked, root7Node72Step2Chunk7_2_checked, root7Node72Step2Chunk7_3_checked, root7Node72Step2Chunk7_4_checked, root7Node72Step2Chunk7_5_checked, root7Node72Step2Chunk8_0_checked, root7Node72Step2Chunk8_1_checked, root7Node72Step2Chunk8_2_checked, root7Node72Step2Chunk8_3_checked, root7Node72Step2Chunk8_4_checked, root7Node72Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root7Node72Leaf_checked :
    checkCover 1 constraints root7Outputs root7Node72Domains2 (.output 35) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
