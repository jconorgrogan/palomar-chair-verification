module

public import SpectreFinite.RadiusThreeRoot8Part21
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable19

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root8Node40Domains0 : Domains 37 State := restrict root8Node39Domains2 9 (5,3)
def root8Node40Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4)]
  | 9 => some [(5,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(6,0)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root8Node40Domains0_fast_eq : root8Node40Domains0 = expandDomains root8Node40Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node40Domains0 v = expandDomains root8Node40Domains0Fast v from by decide) v
theorem root8Node40Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node40Domains0 (.output 18) = true := by decide
def root8Node41Domains0 : Domains 37 State := restrict root8Node39Domains2 9 (8,3)
def root8Node41Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(1,4)]
  | 9 => some [(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(6,0)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(8,2)]
  | 21 => some [(5,0)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(8,1)]
  | 33 => some [(7,4)]
  | 34 => some [(1,3)]
  | 35 => some [(4,2)]
  | _ => some [(5,3)]
theorem root8Node41Domains0_fast_eq : root8Node41Domains0 = expandDomains root8Node41Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node41Domains0 v = expandDomains root8Node41Domains0Fast v from by decide) v
theorem root8Node41Leaf_checked :
    checkCover 1 constraints root8Outputs root8Node41Domains0 (.output 19) = true := by decide
def root8Node42Domains0 : Domains 37 State := restrict root8Node38Domains0 8 (6,4)
def root8Node42Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(6,4)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3),(6,0)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2),(8,2)]
  | 21 => some [(5,0),(5,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4),(8,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(4,1),(8,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5),(1,3),(6,3)]
  | 35 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root8Node42Domains0_fast_eq : root8Node42Domains0 = expandDomains root8Node42Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node42Domains0 v = expandDomains root8Node42Domains0Fast v from by decide) v
def root8Node42Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(4,0)]
  | 1 => [(7,3)]
  | 2 => [(5,2)]
  | 3 => [(8,0)]
  | 4 => [(5,1)]
  | 5 => [(0,1)]
  | 6 => [(6,2)]
  | 7 => [(8,4)]
  | 8 => [(6,4)]
  | 9 => [(5,3),(8,3)]
  | 10 => [(8,5)]
  | 11 => [(1,0)]
  | 12 => [(7,1)]
  | 13 => [(7,5)]
  | 14 => [(0,3)]
  | 15 => [(7,4)]
  | 16 => [(1,3)]
  | 17 => [(8,2)]
  | 18 => [(8,0)]
  | 19 => [(7,3)]
  | 20 => [(4,2)]
  | 21 => [(5,3)]
  | 22 => [(6,5)]
  | 23 => [(0,4)]
  | 24 => [(5,4)]
  | 25 => [(6,4)]
  | 26 => [(1,2)]
  | 27 => [(7,4)]
  | 28 => [(7,0)]
  | 29 => [(4,3)]
  | 30 => [(3,5),(7,5)]
  | 31 => [(0,3)]
  | 32 => [(4,1)]
  | 33 => [(1,4),(7,4)]
  | 34 => [(0,5),(1,3),(6,3)]
  | 35 => [(2,2),(2,4),(4,2)]
  | _ => [(1,3),(3,3),(5,3)]
def root8Node42Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(4,0)]
  | 1 => some [(7,3)]
  | 2 => some [(5,2)]
  | 3 => some [(8,0)]
  | 4 => some [(5,1)]
  | 5 => some [(0,1)]
  | 6 => some [(6,2)]
  | 7 => some [(8,4)]
  | 8 => some [(6,4)]
  | 9 => some [(5,3),(8,3)]
  | 10 => some [(8,5)]
  | 11 => some [(1,0)]
  | 12 => some [(7,1)]
  | 13 => some [(7,5)]
  | 14 => some [(0,3)]
  | 15 => some [(7,4)]
  | 16 => some [(1,3)]
  | 17 => some [(8,2)]
  | 18 => some [(8,0)]
  | 19 => some [(7,3)]
  | 20 => some [(4,2)]
  | 21 => some [(5,3)]
  | 22 => some [(6,5)]
  | 23 => some [(0,4)]
  | 24 => some [(5,4)]
  | 25 => some [(6,4)]
  | 26 => some [(1,2)]
  | 27 => some [(7,4)]
  | 28 => some [(7,0)]
  | 29 => some [(4,3)]
  | 30 => some [(3,5),(7,5)]
  | 31 => some [(0,3)]
  | 32 => some [(4,1)]
  | 33 => some [(1,4),(7,4)]
  | 34 => some [(0,5),(1,3),(6,3)]
  | 35 => some [(2,2),(2,4),(4,2)]
  | _ => some [(1,3),(3,3),(5,3)]
theorem root8Node42Domains1_fast_eq : root8Node42Domains1 = expandDomains root8Node42Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root8Node42Domains1 v = expandDomains root8Node42Domains1Fast v from by decide) v
theorem root8Node42Step1Chunk0_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk0_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk0_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk0_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk0_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk0_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows0_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk1_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows1_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk2_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows2_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk3_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows3_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk4_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows4_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk5_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows5_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk6_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows6_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk7_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows7_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_0_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_0⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_1_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_1⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_2_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_2⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_3_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_3⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_4_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_4⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1Chunk8_5_checked :
    checkNarrowing ⟨table19Scope, table19Rows8_5⟩
      root8Node42Domains0 root8Node42Domains1 = true := by
  exact checkNarrowing_of_fast _ root8Node42Domains0 root8Node42Domains1
    root8Node42Domains0Fast root8Node42Domains1Fast
    root8Node42Domains0_fast_eq root8Node42Domains1_fast_eq (by decide)
theorem root8Node42Step1_checked :
    checkReplacement table19 root8Node42Domains0 root8Node42Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root8Node42Step1Chunk0_0_checked, root8Node42Step1Chunk0_1_checked, root8Node42Step1Chunk0_2_checked, root8Node42Step1Chunk0_3_checked, root8Node42Step1Chunk0_4_checked, root8Node42Step1Chunk0_5_checked, root8Node42Step1Chunk1_0_checked, root8Node42Step1Chunk1_1_checked, root8Node42Step1Chunk1_2_checked, root8Node42Step1Chunk1_3_checked, root8Node42Step1Chunk1_4_checked, root8Node42Step1Chunk1_5_checked, root8Node42Step1Chunk2_0_checked, root8Node42Step1Chunk2_1_checked, root8Node42Step1Chunk2_2_checked, root8Node42Step1Chunk2_3_checked, root8Node42Step1Chunk2_4_checked, root8Node42Step1Chunk2_5_checked, root8Node42Step1Chunk3_0_checked, root8Node42Step1Chunk3_1_checked, root8Node42Step1Chunk3_2_checked, root8Node42Step1Chunk3_3_checked, root8Node42Step1Chunk3_4_checked, root8Node42Step1Chunk3_5_checked, root8Node42Step1Chunk4_0_checked, root8Node42Step1Chunk4_1_checked, root8Node42Step1Chunk4_2_checked, root8Node42Step1Chunk4_3_checked, root8Node42Step1Chunk4_4_checked, root8Node42Step1Chunk4_5_checked, root8Node42Step1Chunk5_0_checked, root8Node42Step1Chunk5_1_checked, root8Node42Step1Chunk5_2_checked, root8Node42Step1Chunk5_3_checked, root8Node42Step1Chunk5_4_checked, root8Node42Step1Chunk5_5_checked, root8Node42Step1Chunk6_0_checked, root8Node42Step1Chunk6_1_checked, root8Node42Step1Chunk6_2_checked, root8Node42Step1Chunk6_3_checked, root8Node42Step1Chunk6_4_checked, root8Node42Step1Chunk6_5_checked, root8Node42Step1Chunk7_0_checked, root8Node42Step1Chunk7_1_checked, root8Node42Step1Chunk7_2_checked, root8Node42Step1Chunk7_3_checked, root8Node42Step1Chunk7_4_checked, root8Node42Step1Chunk7_5_checked, root8Node42Step1Chunk8_0_checked, root8Node42Step1Chunk8_1_checked, root8Node42Step1Chunk8_2_checked, root8Node42Step1Chunk8_3_checked, root8Node42Step1Chunk8_4_checked, root8Node42Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
