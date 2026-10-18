module

public import SpectreFinite.RadiusFourRoot8Part25
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable39

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node83Domains0 : Domains 61 State := restrict root8Node82Domains2 25 (3,1)
def root8Node83Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
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
theorem root8Node83Domains0_fast_eq : root8Node83Domains0 = expandDomains root8Node83Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node83Domains0 v = expandDomains root8Node83Domains0Fast v from by decide) v
def root8Node84Domains0 : Domains 61 State := restrict root8Node83Domains0 55 (5,5)
def root8Node84Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
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
theorem root8Node84Domains0_fast_eq : root8Node84Domains0 = expandDomains root8Node84Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node84Domains0 v = expandDomains root8Node84Domains0Fast v from by decide) v
def root8Node84Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(3,1)]
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
def root8Node84Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
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
theorem root8Node84Domains1_fast_eq : root8Node84Domains1 = expandDomains root8Node84Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node84Domains1 v = expandDomains root8Node84Domains1Fast v from by decide) v
theorem root8Node84Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root8Node84Domains0 root8Node84Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node84Domains0 root8Node84Domains1
    root8Node84Domains0Fast root8Node84Domains1Fast
    root8Node84Domains0_fast_eq root8Node84Domains1_fast_eq (by decide)
theorem root8Node84Step1_checked :
    checkReplacement table39 root8Node84Domains0 root8Node84Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node84Step1Chunk0_0_checked, root8Node84Step1Chunk0_1_checked, root8Node84Step1Chunk0_2_checked, root8Node84Step1Chunk0_3_checked, root8Node84Step1Chunk0_4_checked, root8Node84Step1Chunk0_5_checked, root8Node84Step1Chunk1_0_checked, root8Node84Step1Chunk1_1_checked, root8Node84Step1Chunk1_2_checked, root8Node84Step1Chunk1_3_checked, root8Node84Step1Chunk1_4_checked, root8Node84Step1Chunk1_5_checked, root8Node84Step1Chunk2_0_checked, root8Node84Step1Chunk2_1_checked, root8Node84Step1Chunk2_2_checked, root8Node84Step1Chunk2_3_checked, root8Node84Step1Chunk2_4_checked, root8Node84Step1Chunk2_5_checked, root8Node84Step1Chunk3_0_checked, root8Node84Step1Chunk3_1_checked, root8Node84Step1Chunk3_2_checked, root8Node84Step1Chunk3_3_checked, root8Node84Step1Chunk3_4_checked, root8Node84Step1Chunk3_5_checked, root8Node84Step1Chunk4_0_checked, root8Node84Step1Chunk4_1_checked, root8Node84Step1Chunk4_2_checked, root8Node84Step1Chunk4_3_checked, root8Node84Step1Chunk4_4_checked, root8Node84Step1Chunk4_5_checked, root8Node84Step1Chunk5_0_checked, root8Node84Step1Chunk5_1_checked, root8Node84Step1Chunk5_2_checked, root8Node84Step1Chunk5_3_checked, root8Node84Step1Chunk5_4_checked, root8Node84Step1Chunk5_5_checked, root8Node84Step1Chunk6_0_checked, root8Node84Step1Chunk6_1_checked, root8Node84Step1Chunk6_2_checked, root8Node84Step1Chunk6_3_checked, root8Node84Step1Chunk6_4_checked, root8Node84Step1Chunk6_5_checked, root8Node84Step1Chunk7_0_checked, root8Node84Step1Chunk7_1_checked, root8Node84Step1Chunk7_2_checked, root8Node84Step1Chunk7_3_checked, root8Node84Step1Chunk7_4_checked, root8Node84Step1Chunk7_5_checked, root8Node84Step1Chunk8_0_checked, root8Node84Step1Chunk8_1_checked, root8Node84Step1Chunk8_2_checked, root8Node84Step1Chunk8_3_checked, root8Node84Step1Chunk8_4_checked, root8Node84Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node84Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node84Domains1 (.output 40) = true := by decide
def root8Node85Domains0 : Domains 61 State := restrict root8Node83Domains0 55 (8,5)
def root8Node85Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
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
theorem root8Node85Domains0_fast_eq : root8Node85Domains0 = expandDomains root8Node85Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node85Domains0 v = expandDomains root8Node85Domains0Fast v from by decide) v
def root8Node85Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
  | 22 => [(7,1)]
  | 23 => [(7,5)]
  | 24 => [(6,0)]
  | 25 => [(3,1)]
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
def root8Node85Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
  | 22 => some [(7,1)]
  | 23 => some [(7,5)]
  | 24 => some [(6,0)]
  | 25 => some [(3,1)]
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
theorem root8Node85Domains1_fast_eq : root8Node85Domains1 = expandDomains root8Node85Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node85Domains1 v = expandDomains root8Node85Domains1Fast v from by decide) v
theorem root8Node85Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root8Node85Domains0 root8Node85Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node85Domains0 root8Node85Domains1
    root8Node85Domains0Fast root8Node85Domains1Fast
    root8Node85Domains0_fast_eq root8Node85Domains1_fast_eq (by decide)
theorem root8Node85Step1_checked :
    checkReplacement table39 root8Node85Domains0 root8Node85Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node85Step1Chunk0_0_checked, root8Node85Step1Chunk0_1_checked, root8Node85Step1Chunk0_2_checked, root8Node85Step1Chunk0_3_checked, root8Node85Step1Chunk0_4_checked, root8Node85Step1Chunk0_5_checked, root8Node85Step1Chunk1_0_checked, root8Node85Step1Chunk1_1_checked, root8Node85Step1Chunk1_2_checked, root8Node85Step1Chunk1_3_checked, root8Node85Step1Chunk1_4_checked, root8Node85Step1Chunk1_5_checked, root8Node85Step1Chunk2_0_checked, root8Node85Step1Chunk2_1_checked, root8Node85Step1Chunk2_2_checked, root8Node85Step1Chunk2_3_checked, root8Node85Step1Chunk2_4_checked, root8Node85Step1Chunk2_5_checked, root8Node85Step1Chunk3_0_checked, root8Node85Step1Chunk3_1_checked, root8Node85Step1Chunk3_2_checked, root8Node85Step1Chunk3_3_checked, root8Node85Step1Chunk3_4_checked, root8Node85Step1Chunk3_5_checked, root8Node85Step1Chunk4_0_checked, root8Node85Step1Chunk4_1_checked, root8Node85Step1Chunk4_2_checked, root8Node85Step1Chunk4_3_checked, root8Node85Step1Chunk4_4_checked, root8Node85Step1Chunk4_5_checked, root8Node85Step1Chunk5_0_checked, root8Node85Step1Chunk5_1_checked, root8Node85Step1Chunk5_2_checked, root8Node85Step1Chunk5_3_checked, root8Node85Step1Chunk5_4_checked, root8Node85Step1Chunk5_5_checked, root8Node85Step1Chunk6_0_checked, root8Node85Step1Chunk6_1_checked, root8Node85Step1Chunk6_2_checked, root8Node85Step1Chunk6_3_checked, root8Node85Step1Chunk6_4_checked, root8Node85Step1Chunk6_5_checked, root8Node85Step1Chunk7_0_checked, root8Node85Step1Chunk7_1_checked, root8Node85Step1Chunk7_2_checked, root8Node85Step1Chunk7_3_checked, root8Node85Step1Chunk7_4_checked, root8Node85Step1Chunk7_5_checked, root8Node85Step1Chunk8_0_checked, root8Node85Step1Chunk8_1_checked, root8Node85Step1Chunk8_2_checked, root8Node85Step1Chunk8_3_checked, root8Node85Step1Chunk8_4_checked, root8Node85Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node85Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node85Domains1 (.output 41) = true := by decide
def root8Node86Domains0 : Domains 61 State := restrict root8Node82Domains2 25 (7,1)
def root8Node86Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
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
theorem root8Node86Domains0_fast_eq : root8Node86Domains0 = expandDomains root8Node86Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node86Domains0 v = expandDomains root8Node86Domains0Fast v from by decide) v
def root8Node87Domains0 : Domains 61 State := restrict root8Node86Domains0 55 (5,5)
def root8Node87Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
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
theorem root8Node87Domains0_fast_eq : root8Node87Domains0 = expandDomains root8Node87Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node87Domains0 v = expandDomains root8Node87Domains0Fast v from by decide) v
def root8Node87Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(0,2)]
  | 1 => [(1,1)]
  | 2 => [(8,1)]
  | 3 => [(6,5)]
  | 4 => [(0,4)]
  | 5 => [(5,2)]
  | 6 => [(8,0)]
  | 7 => [(8,3)]
  | 8 => [(5,5)]
  | 9 => [(7,0)]
  | 10 => [(4,3)]
  | 11 => [(0,4)]
  | 12 => [(5,4)]
  | 13 => [(1,4)]
  | 14 => [(0,5)]
  | 15 => [(4,4)]
  | 16 => [(1,4)]
  | 17 => [(0,5)]
  | 18 => [(7,0)]
  | 19 => [(4,3)]
  | 20 => [(7,5)]
  | 21 => [(6,0)]
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
def root8Node87Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(0,2)]
  | 1 => some [(1,1)]
  | 2 => some [(8,1)]
  | 3 => some [(6,5)]
  | 4 => some [(0,4)]
  | 5 => some [(5,2)]
  | 6 => some [(8,0)]
  | 7 => some [(8,3)]
  | 8 => some [(5,5)]
  | 9 => some [(7,0)]
  | 10 => some [(4,3)]
  | 11 => some [(0,4)]
  | 12 => some [(5,4)]
  | 13 => some [(1,4)]
  | 14 => some [(0,5)]
  | 15 => some [(4,4)]
  | 16 => some [(1,4)]
  | 17 => some [(0,5)]
  | 18 => some [(7,0)]
  | 19 => some [(4,3)]
  | 20 => some [(7,5)]
  | 21 => some [(6,0)]
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
theorem root8Node87Domains1_fast_eq : root8Node87Domains1 = expandDomains root8Node87Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root8Node87Domains1 v = expandDomains root8Node87Domains1Fast v from by decide) v
theorem root8Node87Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root8Node87Domains0 root8Node87Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node87Domains0 root8Node87Domains1
    root8Node87Domains0Fast root8Node87Domains1Fast
    root8Node87Domains0_fast_eq root8Node87Domains1_fast_eq (by decide)
theorem root8Node87Step1_checked :
    checkReplacement table39 root8Node87Domains0 root8Node87Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node87Step1Chunk0_0_checked, root8Node87Step1Chunk0_1_checked, root8Node87Step1Chunk0_2_checked, root8Node87Step1Chunk0_3_checked, root8Node87Step1Chunk0_4_checked, root8Node87Step1Chunk0_5_checked, root8Node87Step1Chunk1_0_checked, root8Node87Step1Chunk1_1_checked, root8Node87Step1Chunk1_2_checked, root8Node87Step1Chunk1_3_checked, root8Node87Step1Chunk1_4_checked, root8Node87Step1Chunk1_5_checked, root8Node87Step1Chunk2_0_checked, root8Node87Step1Chunk2_1_checked, root8Node87Step1Chunk2_2_checked, root8Node87Step1Chunk2_3_checked, root8Node87Step1Chunk2_4_checked, root8Node87Step1Chunk2_5_checked, root8Node87Step1Chunk3_0_checked, root8Node87Step1Chunk3_1_checked, root8Node87Step1Chunk3_2_checked, root8Node87Step1Chunk3_3_checked, root8Node87Step1Chunk3_4_checked, root8Node87Step1Chunk3_5_checked, root8Node87Step1Chunk4_0_checked, root8Node87Step1Chunk4_1_checked, root8Node87Step1Chunk4_2_checked, root8Node87Step1Chunk4_3_checked, root8Node87Step1Chunk4_4_checked, root8Node87Step1Chunk4_5_checked, root8Node87Step1Chunk5_0_checked, root8Node87Step1Chunk5_1_checked, root8Node87Step1Chunk5_2_checked, root8Node87Step1Chunk5_3_checked, root8Node87Step1Chunk5_4_checked, root8Node87Step1Chunk5_5_checked, root8Node87Step1Chunk6_0_checked, root8Node87Step1Chunk6_1_checked, root8Node87Step1Chunk6_2_checked, root8Node87Step1Chunk6_3_checked, root8Node87Step1Chunk6_4_checked, root8Node87Step1Chunk6_5_checked, root8Node87Step1Chunk7_0_checked, root8Node87Step1Chunk7_1_checked, root8Node87Step1Chunk7_2_checked, root8Node87Step1Chunk7_3_checked, root8Node87Step1Chunk7_4_checked, root8Node87Step1Chunk7_5_checked, root8Node87Step1Chunk8_0_checked, root8Node87Step1Chunk8_1_checked, root8Node87Step1Chunk8_2_checked, root8Node87Step1Chunk8_3_checked, root8Node87Step1Chunk8_4_checked, root8Node87Step1Chunk8_5_checked, Bool.true_and]
  · decide
theorem root8Node87Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node87Domains1 (.output 42) = true := by decide
end SpectreFinite.HexSearch.RadiusFour
