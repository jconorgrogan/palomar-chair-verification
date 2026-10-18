module

public import SpectreFinite.RadiusFourRoot1Part20
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable10
public import SpectreFinite.RadiusFourTable31
public import SpectreFinite.RadiusFourTable36
public import SpectreFinite.RadiusFourTable39
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
def root1Node57Domains0 : Domains 61 State := restrict root1Node56Domains4 10 (3,1)
def root1Node57Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,5)]
  | 6 => some [(6,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(3,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(5,1),(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0)]
  | 42 => some [(5,3),(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(7,3)]
theorem root1Node57Domains0_fast_eq : root1Node57Domains0 = expandDomains root1Node57Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node57Domains0 v = expandDomains root1Node57Domains0Fast v from by decide) v
def root1Node57Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(2,5)]
  | 6 => [(6,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(3,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(4,1),(8,1)]
  | 44 => [(0,2),(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1)]
  | 56 => [(4,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(6,3)]
  | 59 => [(2,0),(2,2),(2,4),(4,4)]
  | _ => [(0,0),(1,3),(3,3),(7,3)]
def root1Node57Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,5)]
  | 6 => some [(6,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(3,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(7,3)]
theorem root1Node57Domains1_fast_eq : root1Node57Domains1 = expandDomains root1Node57Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node57Domains1 v = expandDomains root1Node57Domains1Fast v from by decide) v
theorem root1Node57Step1Chunk0_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk0_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk0_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk0_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk0_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk0_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows0_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk1_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows1_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk2_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows2_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk3_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows3_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk4_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows4_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk5_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows5_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk6_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows6_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk7_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows7_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_0_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_0⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_1_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_1⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_2_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_2⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_3_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_3⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_4_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_4⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1Chunk8_5_checked :
    checkNarrowing ⟨table31Scope, table31Rows8_5⟩
      root1Node57Domains0 root1Node57Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains0 root1Node57Domains1
    root1Node57Domains0Fast root1Node57Domains1Fast
    root1Node57Domains0_fast_eq root1Node57Domains1_fast_eq (by decide)
theorem root1Node57Step1_checked :
    checkReplacement table31 root1Node57Domains0 root1Node57Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node57Step1Chunk0_0_checked, root1Node57Step1Chunk0_1_checked, root1Node57Step1Chunk0_2_checked, root1Node57Step1Chunk0_3_checked, root1Node57Step1Chunk0_4_checked, root1Node57Step1Chunk0_5_checked, root1Node57Step1Chunk1_0_checked, root1Node57Step1Chunk1_1_checked, root1Node57Step1Chunk1_2_checked, root1Node57Step1Chunk1_3_checked, root1Node57Step1Chunk1_4_checked, root1Node57Step1Chunk1_5_checked, root1Node57Step1Chunk2_0_checked, root1Node57Step1Chunk2_1_checked, root1Node57Step1Chunk2_2_checked, root1Node57Step1Chunk2_3_checked, root1Node57Step1Chunk2_4_checked, root1Node57Step1Chunk2_5_checked, root1Node57Step1Chunk3_0_checked, root1Node57Step1Chunk3_1_checked, root1Node57Step1Chunk3_2_checked, root1Node57Step1Chunk3_3_checked, root1Node57Step1Chunk3_4_checked, root1Node57Step1Chunk3_5_checked, root1Node57Step1Chunk4_0_checked, root1Node57Step1Chunk4_1_checked, root1Node57Step1Chunk4_2_checked, root1Node57Step1Chunk4_3_checked, root1Node57Step1Chunk4_4_checked, root1Node57Step1Chunk4_5_checked, root1Node57Step1Chunk5_0_checked, root1Node57Step1Chunk5_1_checked, root1Node57Step1Chunk5_2_checked, root1Node57Step1Chunk5_3_checked, root1Node57Step1Chunk5_4_checked, root1Node57Step1Chunk5_5_checked, root1Node57Step1Chunk6_0_checked, root1Node57Step1Chunk6_1_checked, root1Node57Step1Chunk6_2_checked, root1Node57Step1Chunk6_3_checked, root1Node57Step1Chunk6_4_checked, root1Node57Step1Chunk6_5_checked, root1Node57Step1Chunk7_0_checked, root1Node57Step1Chunk7_1_checked, root1Node57Step1Chunk7_2_checked, root1Node57Step1Chunk7_3_checked, root1Node57Step1Chunk7_4_checked, root1Node57Step1Chunk7_5_checked, root1Node57Step1Chunk8_0_checked, root1Node57Step1Chunk8_1_checked, root1Node57Step1Chunk8_2_checked, root1Node57Step1Chunk8_3_checked, root1Node57Step1Chunk8_4_checked, root1Node57Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node57Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(2,5)]
  | 6 => [(6,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(3,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0)]
  | 25 => [(7,2)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(5,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1)]
  | 56 => [(4,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,0)]
  | _ => [(7,3)]
def root1Node57Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,5)]
  | 6 => some [(6,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(3,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0)]
  | 25 => some [(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(5,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,0)]
  | _ => some [(7,3)]
theorem root1Node57Domains2_fast_eq : root1Node57Domains2 = expandDomains root1Node57Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node57Domains2 v = expandDomains root1Node57Domains2Fast v from by decide) v
theorem root1Node57Step2Chunk0_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_0⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk0_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_1⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk0_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_2⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk0_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_3⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk0_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_4⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk0_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows0_5⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk1_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_0⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk1_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_1⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk1_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_2⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk1_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_3⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk1_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_4⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk1_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows1_5⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk2_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_0⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk2_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_1⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk2_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_2⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk2_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_3⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk2_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_4⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk2_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows2_5⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk3_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_0⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk3_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_1⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk3_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_2⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk3_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_3⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk3_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_4⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk3_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows3_5⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk4_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_0⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk4_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_1⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk4_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_2⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk4_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_3⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk4_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_4⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk4_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows4_5⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk5_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_0⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk5_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_1⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk5_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_2⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk5_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_3⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk5_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_4⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk5_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows5_5⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk6_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_0⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk6_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_1⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk6_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_2⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk6_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_3⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk6_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_4⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk6_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows6_5⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk7_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_0⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk7_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_1⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk7_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_2⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk7_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_3⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk7_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_4⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk7_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows7_5⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk8_0_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_0⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk8_1_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_1⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk8_2_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_2⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk8_3_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_3⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk8_4_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_4⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root1Node57Domains1 root1Node57Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node57Domains1 root1Node57Domains2
    root1Node57Domains1Fast root1Node57Domains2Fast
    root1Node57Domains1_fast_eq root1Node57Domains2_fast_eq (by decide)
theorem root1Node57Step2_checked :
    checkReplacement table46 root1Node57Domains1 root1Node57Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node57Step2Chunk0_0_checked, root1Node57Step2Chunk0_1_checked, root1Node57Step2Chunk0_2_checked, root1Node57Step2Chunk0_3_checked, root1Node57Step2Chunk0_4_checked, root1Node57Step2Chunk0_5_checked, root1Node57Step2Chunk1_0_checked, root1Node57Step2Chunk1_1_checked, root1Node57Step2Chunk1_2_checked, root1Node57Step2Chunk1_3_checked, root1Node57Step2Chunk1_4_checked, root1Node57Step2Chunk1_5_checked, root1Node57Step2Chunk2_0_checked, root1Node57Step2Chunk2_1_checked, root1Node57Step2Chunk2_2_checked, root1Node57Step2Chunk2_3_checked, root1Node57Step2Chunk2_4_checked, root1Node57Step2Chunk2_5_checked, root1Node57Step2Chunk3_0_checked, root1Node57Step2Chunk3_1_checked, root1Node57Step2Chunk3_2_checked, root1Node57Step2Chunk3_3_checked, root1Node57Step2Chunk3_4_checked, root1Node57Step2Chunk3_5_checked, root1Node57Step2Chunk4_0_checked, root1Node57Step2Chunk4_1_checked, root1Node57Step2Chunk4_2_checked, root1Node57Step2Chunk4_3_checked, root1Node57Step2Chunk4_4_checked, root1Node57Step2Chunk4_5_checked, root1Node57Step2Chunk5_0_checked, root1Node57Step2Chunk5_1_checked, root1Node57Step2Chunk5_2_checked, root1Node57Step2Chunk5_3_checked, root1Node57Step2Chunk5_4_checked, root1Node57Step2Chunk5_5_checked, root1Node57Step2Chunk6_0_checked, root1Node57Step2Chunk6_1_checked, root1Node57Step2Chunk6_2_checked, root1Node57Step2Chunk6_3_checked, root1Node57Step2Chunk6_4_checked, root1Node57Step2Chunk6_5_checked, root1Node57Step2Chunk7_0_checked, root1Node57Step2Chunk7_1_checked, root1Node57Step2Chunk7_2_checked, root1Node57Step2Chunk7_3_checked, root1Node57Step2Chunk7_4_checked, root1Node57Step2Chunk7_5_checked, root1Node57Step2Chunk8_0_checked, root1Node57Step2Chunk8_1_checked, root1Node57Step2Chunk8_2_checked, root1Node57Step2Chunk8_3_checked, root1Node57Step2Chunk8_4_checked, root1Node57Step2Chunk8_5_checked, Bool.true_and]
  · decide
theorem root1Node57Leaf_checked :
    checkCover 1 constraints root1Outputs root1Node57Domains2 (.output 28) = true := by decide
def root1Node58Domains0 : Domains 61 State := restrict root1Node56Domains4 10 (7,1)
def root1Node58Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,5)]
  | 6 => some [(6,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(5,1),(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0)]
  | 42 => some [(5,3),(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(7,3)]
theorem root1Node58Domains0_fast_eq : root1Node58Domains0 = expandDomains root1Node58Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node58Domains0 v = expandDomains root1Node58Domains0Fast v from by decide) v
def root1Node58Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(2,5)]
  | 6 => [(6,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0),(8,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0),(6,4)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5),(7,5)]
  | 33 => [(0,3),(6,1)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3),(6,3)]
  | 38 => [(7,2),(8,2)]
  | 39 => [(4,0),(5,0),(8,0)]
  | 40 => [(4,5),(7,3)]
  | 41 => [(4,2),(7,0)]
  | 42 => [(5,3),(8,3)]
  | 43 => [(4,1),(8,1)]
  | 44 => [(0,2),(6,5)]
  | 45 => [(0,4),(1,1)]
  | 46 => [(5,1),(5,4)]
  | 47 => [(0,0),(0,1),(6,4)]
  | 48 => [(1,2),(6,2),(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,2),(5,5),(8,5)]
  | 51 => [(7,0),(8,0)]
  | 52 => [(4,3),(8,3)]
  | 53 => [(1,5),(3,5),(5,5),(7,5)]
  | 54 => [(0,3),(1,0),(6,1)]
  | 55 => [(2,1),(4,1)]
  | 56 => [(4,4),(7,2),(8,4)]
  | 57 => [(1,4),(7,4)]
  | 58 => [(0,5),(6,3)]
  | 59 => [(2,0),(2,2),(2,4),(4,4)]
  | _ => [(0,0),(1,3),(3,3),(7,3)]
def root1Node58Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,5)]
  | 6 => some [(6,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0),(8,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0)]
  | 42 => some [(5,3),(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(7,3)]
theorem root1Node58Domains1_fast_eq : root1Node58Domains1 = expandDomains root1Node58Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node58Domains1 v = expandDomains root1Node58Domains1Fast v from by decide) v
theorem root1Node58Step1Chunk0_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_0⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk0_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_1⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk0_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_2⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk0_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_3⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk0_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_4⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk0_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows0_5⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk1_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_0⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk1_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_1⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk1_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_2⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk1_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_3⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk1_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_4⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk1_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows1_5⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk2_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_0⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk2_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_1⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk2_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_2⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk2_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_3⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk2_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_4⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk2_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows2_5⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk3_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_0⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk3_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_1⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk3_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_2⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk3_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_3⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk3_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_4⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk3_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows3_5⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk4_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_0⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk4_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_1⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk4_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_2⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk4_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_3⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk4_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_4⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk4_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows4_5⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk5_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_0⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk5_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_1⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk5_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_2⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk5_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_3⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk5_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_4⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk5_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows5_5⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk6_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_0⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk6_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_1⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk6_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_2⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk6_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_3⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk6_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_4⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk6_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows6_5⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk7_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_0⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk7_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_1⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk7_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_2⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk7_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_3⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk7_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_4⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk7_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows7_5⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk8_0_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_0⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk8_1_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_1⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk8_2_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_2⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk8_3_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_3⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk8_4_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_4⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1Chunk8_5_checked :
    checkNarrowing ⟨table10Scope, table10Rows8_5⟩
      root1Node58Domains0 root1Node58Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node58Domains0 root1Node58Domains1
    root1Node58Domains0Fast root1Node58Domains1Fast
    root1Node58Domains0_fast_eq root1Node58Domains1_fast_eq (by decide)
theorem root1Node58Step1_checked :
    checkReplacement table10 root1Node58Domains0 root1Node58Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node58Step1Chunk0_0_checked, root1Node58Step1Chunk0_1_checked, root1Node58Step1Chunk0_2_checked, root1Node58Step1Chunk0_3_checked, root1Node58Step1Chunk0_4_checked, root1Node58Step1Chunk0_5_checked, root1Node58Step1Chunk1_0_checked, root1Node58Step1Chunk1_1_checked, root1Node58Step1Chunk1_2_checked, root1Node58Step1Chunk1_3_checked, root1Node58Step1Chunk1_4_checked, root1Node58Step1Chunk1_5_checked, root1Node58Step1Chunk2_0_checked, root1Node58Step1Chunk2_1_checked, root1Node58Step1Chunk2_2_checked, root1Node58Step1Chunk2_3_checked, root1Node58Step1Chunk2_4_checked, root1Node58Step1Chunk2_5_checked, root1Node58Step1Chunk3_0_checked, root1Node58Step1Chunk3_1_checked, root1Node58Step1Chunk3_2_checked, root1Node58Step1Chunk3_3_checked, root1Node58Step1Chunk3_4_checked, root1Node58Step1Chunk3_5_checked, root1Node58Step1Chunk4_0_checked, root1Node58Step1Chunk4_1_checked, root1Node58Step1Chunk4_2_checked, root1Node58Step1Chunk4_3_checked, root1Node58Step1Chunk4_4_checked, root1Node58Step1Chunk4_5_checked, root1Node58Step1Chunk5_0_checked, root1Node58Step1Chunk5_1_checked, root1Node58Step1Chunk5_2_checked, root1Node58Step1Chunk5_3_checked, root1Node58Step1Chunk5_4_checked, root1Node58Step1Chunk5_5_checked, root1Node58Step1Chunk6_0_checked, root1Node58Step1Chunk6_1_checked, root1Node58Step1Chunk6_2_checked, root1Node58Step1Chunk6_3_checked, root1Node58Step1Chunk6_4_checked, root1Node58Step1Chunk6_5_checked, root1Node58Step1Chunk7_0_checked, root1Node58Step1Chunk7_1_checked, root1Node58Step1Chunk7_2_checked, root1Node58Step1Chunk7_3_checked, root1Node58Step1Chunk7_4_checked, root1Node58Step1Chunk7_5_checked, root1Node58Step1Chunk8_0_checked, root1Node58Step1Chunk8_1_checked, root1Node58Step1Chunk8_2_checked, root1Node58Step1Chunk8_3_checked, root1Node58Step1Chunk8_4_checked, root1Node58Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node59Domains0 : Domains 61 State := restrict root1Node58Domains1 16 (5,0)
def root1Node59Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,5)]
  | 6 => some [(6,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0),(6,4)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5),(7,5)]
  | 33 => some [(0,3),(6,1)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3),(6,3)]
  | 38 => some [(7,2),(8,2)]
  | 39 => some [(4,0),(5,0),(8,0)]
  | 40 => some [(4,5),(7,3)]
  | 41 => some [(4,2),(7,0)]
  | 42 => some [(5,3),(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(0,2),(6,5)]
  | 45 => some [(0,4),(1,1)]
  | 46 => some [(5,1),(5,4)]
  | 47 => some [(0,0),(0,1),(6,4)]
  | 48 => some [(1,2),(6,2),(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0),(8,0)]
  | 52 => some [(4,3),(8,3)]
  | 53 => some [(1,5),(3,5),(5,5),(7,5)]
  | 54 => some [(0,3),(1,0),(6,1)]
  | 55 => some [(2,1),(4,1)]
  | 56 => some [(4,4),(7,2),(8,4)]
  | 57 => some [(1,4),(7,4)]
  | 58 => some [(0,5),(6,3)]
  | 59 => some [(2,0),(2,2),(2,4),(4,4)]
  | _ => some [(0,0),(1,3),(3,3),(7,3)]
theorem root1Node59Domains0_fast_eq : root1Node59Domains0 = expandDomains root1Node59Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node59Domains0 v = expandDomains root1Node59Domains0Fast v from by decide) v
def root1Node59Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(2,5)]
  | 6 => [(6,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(4,1),(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,2),(5,5),(8,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1)]
  | 56 => [(4,4),(7,2),(8,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,0)]
  | _ => [(7,3)]
def root1Node59Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,5)]
  | 6 => some [(6,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(4,1),(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,2),(5,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4),(7,2),(8,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,0)]
  | _ => some [(7,3)]
theorem root1Node59Domains1_fast_eq : root1Node59Domains1 = expandDomains root1Node59Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node59Domains1 v = expandDomains root1Node59Domains1Fast v from by decide) v
theorem root1Node59Step1Chunk0_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_0⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk0_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_1⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk0_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_2⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk0_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_3⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk0_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_4⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk0_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows0_5⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk1_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_0⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk1_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_1⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk1_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_2⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk1_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_3⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk1_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_4⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk1_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows1_5⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk2_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_0⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk2_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_1⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk2_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_2⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk2_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_3⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk2_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_4⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk2_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows2_5⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk3_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_0⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk3_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_1⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk3_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_2⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk3_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_3⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk3_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_4⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk3_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows3_5⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk4_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_0⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk4_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_1⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk4_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_2⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk4_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_3⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk4_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_4⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk4_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows4_5⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk5_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_0⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk5_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_1⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk5_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_2⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk5_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_3⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk5_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_4⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk5_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows5_5⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk6_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_0⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk6_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_1⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk6_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_2⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk6_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_3⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk6_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_4⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk6_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows6_5⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk7_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_0⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk7_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_1⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk7_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_2⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk7_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_3⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk7_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_4⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk7_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows7_5⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk8_0_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_0⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk8_1_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_1⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk8_2_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_2⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk8_3_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_3⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk8_4_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_4⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1Chunk8_5_checked :
    checkNarrowing ⟨table39Scope, table39Rows8_5⟩
      root1Node59Domains0 root1Node59Domains1 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains0 root1Node59Domains1
    root1Node59Domains0Fast root1Node59Domains1Fast
    root1Node59Domains0_fast_eq root1Node59Domains1_fast_eq (by decide)
theorem root1Node59Step1_checked :
    checkReplacement table39 root1Node59Domains0 root1Node59Domains1 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node59Step1Chunk0_0_checked, root1Node59Step1Chunk0_1_checked, root1Node59Step1Chunk0_2_checked, root1Node59Step1Chunk0_3_checked, root1Node59Step1Chunk0_4_checked, root1Node59Step1Chunk0_5_checked, root1Node59Step1Chunk1_0_checked, root1Node59Step1Chunk1_1_checked, root1Node59Step1Chunk1_2_checked, root1Node59Step1Chunk1_3_checked, root1Node59Step1Chunk1_4_checked, root1Node59Step1Chunk1_5_checked, root1Node59Step1Chunk2_0_checked, root1Node59Step1Chunk2_1_checked, root1Node59Step1Chunk2_2_checked, root1Node59Step1Chunk2_3_checked, root1Node59Step1Chunk2_4_checked, root1Node59Step1Chunk2_5_checked, root1Node59Step1Chunk3_0_checked, root1Node59Step1Chunk3_1_checked, root1Node59Step1Chunk3_2_checked, root1Node59Step1Chunk3_3_checked, root1Node59Step1Chunk3_4_checked, root1Node59Step1Chunk3_5_checked, root1Node59Step1Chunk4_0_checked, root1Node59Step1Chunk4_1_checked, root1Node59Step1Chunk4_2_checked, root1Node59Step1Chunk4_3_checked, root1Node59Step1Chunk4_4_checked, root1Node59Step1Chunk4_5_checked, root1Node59Step1Chunk5_0_checked, root1Node59Step1Chunk5_1_checked, root1Node59Step1Chunk5_2_checked, root1Node59Step1Chunk5_3_checked, root1Node59Step1Chunk5_4_checked, root1Node59Step1Chunk5_5_checked, root1Node59Step1Chunk6_0_checked, root1Node59Step1Chunk6_1_checked, root1Node59Step1Chunk6_2_checked, root1Node59Step1Chunk6_3_checked, root1Node59Step1Chunk6_4_checked, root1Node59Step1Chunk6_5_checked, root1Node59Step1Chunk7_0_checked, root1Node59Step1Chunk7_1_checked, root1Node59Step1Chunk7_2_checked, root1Node59Step1Chunk7_3_checked, root1Node59Step1Chunk7_4_checked, root1Node59Step1Chunk7_5_checked, root1Node59Step1Chunk8_0_checked, root1Node59Step1Chunk8_1_checked, root1Node59Step1Chunk8_2_checked, root1Node59Step1Chunk8_3_checked, root1Node59Step1Chunk8_4_checked, root1Node59Step1Chunk8_5_checked, Bool.true_and]
  · decide
def root1Node59Domains2 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,4)]
  | 1 => [(0,5)]
  | 2 => [(4,4)]
  | 3 => [(1,4)]
  | 4 => [(0,5)]
  | 5 => [(2,5)]
  | 6 => [(6,0)]
  | 7 => [(7,1)]
  | 8 => [(7,5)]
  | 9 => [(6,0)]
  | 10 => [(7,1)]
  | 11 => [(0,0)]
  | 12 => [(7,2)]
  | 13 => [(4,0)]
  | 14 => [(7,3)]
  | 15 => [(8,2)]
  | 16 => [(5,0)]
  | 17 => [(4,5),(7,3)]
  | 18 => [(1,5)]
  | 19 => [(6,1)]
  | 20 => [(5,1)]
  | 21 => [(0,1)]
  | 22 => [(6,2)]
  | 23 => [(8,4)]
  | 24 => [(0,0)]
  | 25 => [(1,2),(7,2)]
  | 26 => [(4,5)]
  | 27 => [(7,0)]
  | 28 => [(8,3)]
  | 29 => [(8,5)]
  | 30 => [(1,0)]
  | 31 => [(7,1)]
  | 32 => [(1,5)]
  | 33 => [(6,1)]
  | 34 => [(8,1)]
  | 35 => [(7,2)]
  | 36 => [(7,4)]
  | 37 => [(1,3)]
  | 38 => [(8,2)]
  | 39 => [(5,0)]
  | 40 => [(4,5)]
  | 41 => [(7,0)]
  | 42 => [(8,3)]
  | 43 => [(8,1)]
  | 44 => [(6,5)]
  | 45 => [(0,4)]
  | 46 => [(5,4)]
  | 47 => [(0,0)]
  | 48 => [(7,2)]
  | 49 => [(7,4)]
  | 50 => [(5,5)]
  | 51 => [(7,0)]
  | 52 => [(4,3)]
  | 53 => [(1,5)]
  | 54 => [(6,1)]
  | 55 => [(4,1)]
  | 56 => [(4,4)]
  | 57 => [(1,4)]
  | 58 => [(0,5)]
  | 59 => [(2,0)]
  | _ => [(7,3)]
def root1Node59Domains2Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,4)]
  | 1 => some [(0,5)]
  | 2 => some [(4,4)]
  | 3 => some [(1,4)]
  | 4 => some [(0,5)]
  | 5 => some [(2,5)]
  | 6 => some [(6,0)]
  | 7 => some [(7,1)]
  | 8 => some [(7,5)]
  | 9 => some [(6,0)]
  | 10 => some [(7,1)]
  | 11 => some [(0,0)]
  | 12 => some [(7,2)]
  | 13 => some [(4,0)]
  | 14 => some [(7,3)]
  | 15 => some [(8,2)]
  | 16 => some [(5,0)]
  | 17 => some [(4,5),(7,3)]
  | 18 => some [(1,5)]
  | 19 => some [(6,1)]
  | 20 => some [(5,1)]
  | 21 => some [(0,1)]
  | 22 => some [(6,2)]
  | 23 => some [(8,4)]
  | 24 => some [(0,0)]
  | 25 => some [(1,2),(7,2)]
  | 26 => some [(4,5)]
  | 27 => some [(7,0)]
  | 28 => some [(8,3)]
  | 29 => some [(8,5)]
  | 30 => some [(1,0)]
  | 31 => some [(7,1)]
  | 32 => some [(1,5)]
  | 33 => some [(6,1)]
  | 34 => some [(8,1)]
  | 35 => some [(7,2)]
  | 36 => some [(7,4)]
  | 37 => some [(1,3)]
  | 38 => some [(8,2)]
  | 39 => some [(5,0)]
  | 40 => some [(4,5)]
  | 41 => some [(7,0)]
  | 42 => some [(8,3)]
  | 43 => some [(8,1)]
  | 44 => some [(6,5)]
  | 45 => some [(0,4)]
  | 46 => some [(5,4)]
  | 47 => some [(0,0)]
  | 48 => some [(7,2)]
  | 49 => some [(7,4)]
  | 50 => some [(5,5)]
  | 51 => some [(7,0)]
  | 52 => some [(4,3)]
  | 53 => some [(1,5)]
  | 54 => some [(6,1)]
  | 55 => some [(4,1)]
  | 56 => some [(4,4)]
  | 57 => some [(1,4)]
  | 58 => some [(0,5)]
  | 59 => some [(2,0)]
  | _ => some [(7,3)]
theorem root1Node59Domains2_fast_eq : root1Node59Domains2 = expandDomains root1Node59Domains2Fast := by
  funext v
  exact (show ∀ v : Fin 61, root1Node59Domains2 v = expandDomains root1Node59Domains2Fast v from by decide) v
theorem root1Node59Step2Chunk0_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_0⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk0_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_1⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk0_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_2⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk0_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_3⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk0_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_4⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk0_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows0_5⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk1_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_0⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk1_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_1⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk1_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_2⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk1_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_3⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk1_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_4⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk1_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows1_5⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk2_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_0⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk2_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_1⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk2_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_2⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk2_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_3⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk2_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_4⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk2_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows2_5⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk3_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_0⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk3_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_1⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk3_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_2⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk3_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_3⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk3_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_4⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk3_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows3_5⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk4_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_0⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk4_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_1⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk4_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_2⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk4_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_3⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk4_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_4⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk4_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows4_5⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk5_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_0⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk5_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_1⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk5_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_2⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk5_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_3⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk5_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_4⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk5_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows5_5⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk6_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_0⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk6_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_1⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk6_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_2⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk6_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_3⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk6_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_4⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk6_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows6_5⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk7_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_0⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk7_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_1⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk7_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_2⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk7_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_3⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk7_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_4⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk7_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows7_5⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk8_0_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_0⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk8_1_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_1⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk8_2_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_2⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk8_3_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_3⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk8_4_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_4⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2Chunk8_5_checked :
    checkNarrowing ⟨table36Scope, table36Rows8_5⟩
      root1Node59Domains1 root1Node59Domains2 = true := by
  exact checkNarrowing_of_fast _ root1Node59Domains1 root1Node59Domains2
    root1Node59Domains1Fast root1Node59Domains2Fast
    root1Node59Domains1_fast_eq root1Node59Domains2_fast_eq (by decide)
theorem root1Node59Step2_checked :
    checkReplacement table36 root1Node59Domains1 root1Node59Domains2 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root1Node59Step2Chunk0_0_checked, root1Node59Step2Chunk0_1_checked, root1Node59Step2Chunk0_2_checked, root1Node59Step2Chunk0_3_checked, root1Node59Step2Chunk0_4_checked, root1Node59Step2Chunk0_5_checked, root1Node59Step2Chunk1_0_checked, root1Node59Step2Chunk1_1_checked, root1Node59Step2Chunk1_2_checked, root1Node59Step2Chunk1_3_checked, root1Node59Step2Chunk1_4_checked, root1Node59Step2Chunk1_5_checked, root1Node59Step2Chunk2_0_checked, root1Node59Step2Chunk2_1_checked, root1Node59Step2Chunk2_2_checked, root1Node59Step2Chunk2_3_checked, root1Node59Step2Chunk2_4_checked, root1Node59Step2Chunk2_5_checked, root1Node59Step2Chunk3_0_checked, root1Node59Step2Chunk3_1_checked, root1Node59Step2Chunk3_2_checked, root1Node59Step2Chunk3_3_checked, root1Node59Step2Chunk3_4_checked, root1Node59Step2Chunk3_5_checked, root1Node59Step2Chunk4_0_checked, root1Node59Step2Chunk4_1_checked, root1Node59Step2Chunk4_2_checked, root1Node59Step2Chunk4_3_checked, root1Node59Step2Chunk4_4_checked, root1Node59Step2Chunk4_5_checked, root1Node59Step2Chunk5_0_checked, root1Node59Step2Chunk5_1_checked, root1Node59Step2Chunk5_2_checked, root1Node59Step2Chunk5_3_checked, root1Node59Step2Chunk5_4_checked, root1Node59Step2Chunk5_5_checked, root1Node59Step2Chunk6_0_checked, root1Node59Step2Chunk6_1_checked, root1Node59Step2Chunk6_2_checked, root1Node59Step2Chunk6_3_checked, root1Node59Step2Chunk6_4_checked, root1Node59Step2Chunk6_5_checked, root1Node59Step2Chunk7_0_checked, root1Node59Step2Chunk7_1_checked, root1Node59Step2Chunk7_2_checked, root1Node59Step2Chunk7_3_checked, root1Node59Step2Chunk7_4_checked, root1Node59Step2Chunk7_5_checked, root1Node59Step2Chunk8_0_checked, root1Node59Step2Chunk8_1_checked, root1Node59Step2Chunk8_2_checked, root1Node59Step2Chunk8_3_checked, root1Node59Step2Chunk8_4_checked, root1Node59Step2Chunk8_5_checked, Bool.true_and]
  · decide
end SpectreFinite.HexSearch.RadiusFour
