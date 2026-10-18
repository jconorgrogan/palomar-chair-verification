module

public import SpectreFinite.RadiusThreeRoot0Part12
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusThreeTable13

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusThree
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root0Node21Domains0 : Domains 37 State := restrict root0Node20Domains1 36 (1,3)
def root0Node21Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(2,0)]
  | 3 => some [(7,3)]
  | 4 => some [(7,5)]
  | 5 => some [(6,0)]
  | 6 => some [(3,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(7,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(1,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,4)]
  | 16 => some [(1,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0)]
  | 21 => some [(7,3)]
  | 22 => some [(0,3)]
  | 23 => some [(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(5,1)]
  | 27 => some [(0,1)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(7,4)]
  | _ => some [(1,3)]
theorem root0Node21Domains0_fast_eq : root0Node21Domains0 = expandDomains root0Node21Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node21Domains0 v = expandDomains root0Node21Domains0Fast v from by decide) v
theorem root0Node21Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node21Domains0 (.output 9) = true := by decide
def root0Node22Domains0 : Domains 37 State := restrict root0Node20Domains1 36 (6,3)
def root0Node22Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(2,0)]
  | 3 => some [(7,3)]
  | 4 => some [(7,5)]
  | 5 => some [(6,0)]
  | 6 => some [(3,1)]
  | 7 => some [(0,1)]
  | 8 => some [(6,2)]
  | 9 => some [(7,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(1,0)]
  | 14 => some [(7,1)]
  | 15 => some [(6,4)]
  | 16 => some [(1,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0)]
  | 21 => some [(7,3)]
  | 22 => some [(0,3)]
  | 23 => some [(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(5,1)]
  | 27 => some [(0,1)]
  | 28 => some [(5,3)]
  | 29 => some [(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(8,3)]
  | 32 => some [(8,5)]
  | 33 => some [(6,3)]
  | 34 => some [(7,2)]
  | 35 => some [(7,4)]
  | _ => some [(6,3)]
theorem root0Node22Domains0_fast_eq : root0Node22Domains0 = expandDomains root0Node22Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node22Domains0 v = expandDomains root0Node22Domains0Fast v from by decide) v
theorem root0Node22Leaf_checked :
    checkCover 1 constraints root0Outputs root0Node22Domains0 (.output 10) = true := by decide
def root0Node23Domains0 : Domains 37 State := restrict root0Node15Domains1 6 (7,1)
def root0Node23Domains0Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(2,0),(2,4),(4,4)]
  | 3 => some [(0,0),(1,3),(7,3)]
  | 4 => some [(7,5)]
  | 5 => some [(6,0)]
  | 6 => some [(7,1)]
  | 7 => some [(0,1),(1,5),(6,5)]
  | 8 => some [(0,4),(6,1),(6,2)]
  | 9 => some [(7,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(1,0),(7,0)]
  | 14 => some [(4,3),(7,1),(8,3)]
  | 15 => some [(0,1),(6,4)]
  | 16 => some [(1,2),(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(4,0),(7,4)]
  | 21 => some [(1,3),(6,3),(7,3)]
  | 22 => some [(0,3),(1,0)]
  | 23 => some [(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(5,1),(8,1)]
  | 27 => some [(0,1),(0,2),(6,5)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,3)]
  | 34 => some [(4,4),(7,2)]
  | 35 => some [(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,3)]
theorem root0Node23Domains0_fast_eq : root0Node23Domains0 = expandDomains root0Node23Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node23Domains0 v = expandDomains root0Node23Domains0Fast v from by decide) v
def root0Node23Domains1 (v : Fin 37) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(2,4),(4,4)]
  | 3 => [(0,0),(1,3)]
  | 4 => [(7,5)]
  | 5 => [(6,0)]
  | 6 => [(7,1)]
  | 7 => [(1,5),(6,5)]
  | 8 => [(0,4),(6,1)]
  | 9 => [(7,3)]
  | 10 => [(8,2)]
  | 11 => [(5,0)]
  | 12 => [(4,5)]
  | 13 => [(7,0)]
  | 14 => [(4,3),(8,3)]
  | 15 => [(0,1),(6,4)]
  | 16 => [(1,2),(6,2)]
  | 17 => [(8,4)]
  | 18 => [(0,0)]
  | 19 => [(7,2)]
  | 20 => [(7,4)]
  | 21 => [(1,3),(6,3)]
  | 22 => [(0,3),(1,0)]
  | 23 => [(7,1),(8,1)]
  | 24 => [(1,5)]
  | 25 => [(6,1)]
  | 26 => [(4,1),(8,1)]
  | 27 => [(0,2),(6,5)]
  | 28 => [(5,0),(5,3)]
  | 29 => [(4,5),(5,5),(8,5)]
  | 30 => [(7,0)]
  | 31 => [(7,3),(8,3)]
  | 32 => [(5,2),(5,5),(8,5)]
  | 33 => [(0,0),(0,5),(6,3)]
  | 34 => [(4,4),(7,2)]
  | 35 => [(1,4),(6,4),(7,4)]
  | _ => [(0,5),(1,2),(1,3),(6,3)]
def root0Node23Domains1Fast (v : Fin 37) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(2,4),(4,4)]
  | 3 => some [(0,0),(1,3)]
  | 4 => some [(7,5)]
  | 5 => some [(6,0)]
  | 6 => some [(7,1)]
  | 7 => some [(1,5),(6,5)]
  | 8 => some [(0,4),(6,1)]
  | 9 => some [(7,3)]
  | 10 => some [(8,2)]
  | 11 => some [(5,0)]
  | 12 => some [(4,5)]
  | 13 => some [(7,0)]
  | 14 => some [(4,3),(8,3)]
  | 15 => some [(0,1),(6,4)]
  | 16 => some [(1,2),(6,2)]
  | 17 => some [(8,4)]
  | 18 => some [(0,0)]
  | 19 => some [(7,2)]
  | 20 => some [(7,4)]
  | 21 => some [(1,3),(6,3)]
  | 22 => some [(0,3),(1,0)]
  | 23 => some [(7,1),(8,1)]
  | 24 => some [(1,5)]
  | 25 => some [(6,1)]
  | 26 => some [(4,1),(8,1)]
  | 27 => some [(0,2),(6,5)]
  | 28 => some [(5,0),(5,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(7,3),(8,3)]
  | 32 => some [(5,2),(5,5),(8,5)]
  | 33 => some [(0,0),(0,5),(6,3)]
  | 34 => some [(4,4),(7,2)]
  | 35 => some [(1,4),(6,4),(7,4)]
  | _ => some [(0,5),(1,2),(1,3),(6,3)]
theorem root0Node23Domains1_fast_eq : root0Node23Domains1 = expandDomains root0Node23Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 37, root0Node23Domains1 v = expandDomains root0Node23Domains1Fast v from by decide) v
theorem root0Node23Step1Chunk0_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk0_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows0_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk1_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows1_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk2_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows2_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk3_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows3_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk4_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows4_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk5_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows5_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk6_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows6_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk7_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows7_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_0_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_0⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_1_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_1⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_2_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_2⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_3_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_3⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_4_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_4⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1Chunk8_5_checked :
    checkNarrowing ⟨table13Scope, table13Rows8_5⟩
      root0Node23Domains0 root0Node23Domains1 = true := by
  exact checkNarrowing_of_fast _ root0Node23Domains0 root0Node23Domains1
    root0Node23Domains0Fast root0Node23Domains1Fast
    root0Node23Domains0_fast_eq root0Node23Domains1_fast_eq (by decide)
theorem root0Node23Step1_checked :
    checkReplacement table13 root0Node23Domains0 root0Node23Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root0Node23Step1Chunk0_0_checked, root0Node23Step1Chunk0_1_checked, root0Node23Step1Chunk0_2_checked, root0Node23Step1Chunk0_3_checked, root0Node23Step1Chunk0_4_checked, root0Node23Step1Chunk0_5_checked, root0Node23Step1Chunk1_0_checked, root0Node23Step1Chunk1_1_checked, root0Node23Step1Chunk1_2_checked, root0Node23Step1Chunk1_3_checked, root0Node23Step1Chunk1_4_checked, root0Node23Step1Chunk1_5_checked, root0Node23Step1Chunk2_0_checked, root0Node23Step1Chunk2_1_checked, root0Node23Step1Chunk2_2_checked, root0Node23Step1Chunk2_3_checked, root0Node23Step1Chunk2_4_checked, root0Node23Step1Chunk2_5_checked, root0Node23Step1Chunk3_0_checked, root0Node23Step1Chunk3_1_checked, root0Node23Step1Chunk3_2_checked, root0Node23Step1Chunk3_3_checked, root0Node23Step1Chunk3_4_checked, root0Node23Step1Chunk3_5_checked, root0Node23Step1Chunk4_0_checked, root0Node23Step1Chunk4_1_checked, root0Node23Step1Chunk4_2_checked, root0Node23Step1Chunk4_3_checked, root0Node23Step1Chunk4_4_checked, root0Node23Step1Chunk4_5_checked, root0Node23Step1Chunk5_0_checked, root0Node23Step1Chunk5_1_checked, root0Node23Step1Chunk5_2_checked, root0Node23Step1Chunk5_3_checked, root0Node23Step1Chunk5_4_checked, root0Node23Step1Chunk5_5_checked, root0Node23Step1Chunk6_0_checked, root0Node23Step1Chunk6_1_checked, root0Node23Step1Chunk6_2_checked, root0Node23Step1Chunk6_3_checked, root0Node23Step1Chunk6_4_checked, root0Node23Step1Chunk6_5_checked, root0Node23Step1Chunk7_0_checked, root0Node23Step1Chunk7_1_checked, root0Node23Step1Chunk7_2_checked, root0Node23Step1Chunk7_3_checked, root0Node23Step1Chunk7_4_checked, root0Node23Step1Chunk7_5_checked, root0Node23Step1Chunk8_0_checked, root0Node23Step1Chunk8_1_checked, root0Node23Step1Chunk8_2_checked, root0Node23Step1Chunk8_3_checked, root0Node23Step1Chunk8_4_checked, root0Node23Step1Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusThree
