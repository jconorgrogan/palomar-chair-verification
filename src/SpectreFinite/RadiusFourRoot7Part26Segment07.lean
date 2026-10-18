module

public import SpectreFinite.RadiusFourRoot7Part26Segment06
public import SpectreFinite.RadiusFourRoot7Part25
public import SpectreFinite.RadiusThreeChunkChecking
public import SpectreFinite.RadiusThreeFastChecking
public import SpectreFinite.RadiusFourTable19
public import SpectreFinite.RadiusFourTable23
public import SpectreFinite.RadiusFourTable29
public import SpectreFinite.RadiusFourTable46

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFour
open SpectreFinite.FiniteTable
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open HigherFastChecking
theorem root7Node80Step3Chunk8_5_checked :
    checkNarrowing ⟨table46Scope, table46Rows8_5⟩
      root7Node80Domains2 root7Node80Domains3 = true := by
  exact checkNarrowing_of_fast _ root7Node80Domains2 root7Node80Domains3
    root7Node80Domains2Fast root7Node80Domains3Fast
    root7Node80Domains2_fast_eq root7Node80Domains3_fast_eq (by decide)
theorem root7Node80Step3_checked :
    checkReplacement table46 root7Node80Domains2 root7Node80Domains3 = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply checkNarrowing_flatten
    simp only [List.all_cons, List.all_nil, root7Node80Step3Chunk0_0_checked, root7Node80Step3Chunk0_1_checked, root7Node80Step3Chunk0_2_checked, root7Node80Step3Chunk0_3_checked, root7Node80Step3Chunk0_4_checked, root7Node80Step3Chunk0_5_checked, root7Node80Step3Chunk1_0_checked, root7Node80Step3Chunk1_1_checked, root7Node80Step3Chunk1_2_checked, root7Node80Step3Chunk1_3_checked, root7Node80Step3Chunk1_4_checked, root7Node80Step3Chunk1_5_checked, root7Node80Step3Chunk2_0_checked, root7Node80Step3Chunk2_1_checked, root7Node80Step3Chunk2_2_checked, root7Node80Step3Chunk2_3_checked, root7Node80Step3Chunk2_4_checked, root7Node80Step3Chunk2_5_checked, root7Node80Step3Chunk3_0_checked, root7Node80Step3Chunk3_1_checked, root7Node80Step3Chunk3_2_checked, root7Node80Step3Chunk3_3_checked, root7Node80Step3Chunk3_4_checked, root7Node80Step3Chunk3_5_checked, root7Node80Step3Chunk4_0_checked, root7Node80Step3Chunk4_1_checked, root7Node80Step3Chunk4_2_checked, root7Node80Step3Chunk4_3_checked, root7Node80Step3Chunk4_4_checked, root7Node80Step3Chunk4_5_checked, root7Node80Step3Chunk5_0_checked, root7Node80Step3Chunk5_1_checked, root7Node80Step3Chunk5_2_checked, root7Node80Step3Chunk5_3_checked, root7Node80Step3Chunk5_4_checked, root7Node80Step3Chunk5_5_checked, root7Node80Step3Chunk6_0_checked, root7Node80Step3Chunk6_1_checked, root7Node80Step3Chunk6_2_checked, root7Node80Step3Chunk6_3_checked, root7Node80Step3Chunk6_4_checked, root7Node80Step3Chunk6_5_checked, root7Node80Step3Chunk7_0_checked, root7Node80Step3Chunk7_1_checked, root7Node80Step3Chunk7_2_checked, root7Node80Step3Chunk7_3_checked, root7Node80Step3Chunk7_4_checked, root7Node80Step3Chunk7_5_checked, root7Node80Step3Chunk8_0_checked, root7Node80Step3Chunk8_1_checked, root7Node80Step3Chunk8_2_checked, root7Node80Step3Chunk8_3_checked, root7Node80Step3Chunk8_4_checked, root7Node80Step3Chunk8_5_checked, Bool.true_and]
  · decide
def root7Node81Domains0 : Domains 61 State := restrict root7Node80Domains3 13 (2,4)
def root7Node81Domains0Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5),(5,4),(6,5),(7,5)]
  | 1 => some [(0,3),(0,4),(6,1),(6,4)]
  | 2 => some [(1,2),(5,1),(5,4)]
  | 3 => some [(0,1),(1,4),(6,4),(7,4)]
  | 4 => some [(0,5),(1,2),(6,2),(6,3)]
  | 5 => some [(4,3),(4,5),(7,3),(8,5)]
  | 6 => some [(3,5),(4,2),(7,0)]
  | 7 => some [(0,3),(4,3),(5,3),(8,3)]
  | 8 => some [(4,1),(7,5),(8,5)]
  | 9 => some [(0,2),(0,3),(1,0),(6,0)]
  | 10 => some [(1,1),(7,1),(8,1)]
  | 11 => some [(0,0),(1,4),(6,3),(6,4)]
  | 12 => some [(0,5),(1,2),(7,2)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(4,2),(5,2),(8,2)]
  | 16 => some [(5,0),(5,3),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3),(8,5)]
  | 18 => some [(0,2),(1,5),(7,5)]
  | 19 => some [(0,3),(1,1),(6,0),(6,1)]
  | 20 => some [(7,1),(8,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(3,4),(5,4)]
  | 24 => some [(0,0),(1,4),(6,3),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(1,3),(4,5),(5,2),(5,5),(7,3),(8,5)]
  | 27 => some [(4,2),(7,0),(8,0),(8,2)]
  | 28 => some [(5,0),(5,3),(8,3)]
  | 29 => some [(4,5),(5,5),(8,5)]
  | 30 => some [(7,0)]
  | 31 => some [(2,3),(4,3)]
  | 32 => some [(0,2),(1,5),(3,5),(7,5)]
  | 33 => some [(0,3),(1,1),(6,0),(6,1)]
  | 34 => some [(4,1),(7,1),(8,1)]
  | 35 => some [(0,4),(1,2),(4,4),(5,4),(6,2),(7,2),(8,4)]
  | 36 => some [(1,4),(3,4),(7,4),(8,4)]
  | 37 => some [(0,0),(0,5),(6,3)]
  | 38 => some [(4,4),(7,2)]
  | 39 => some [(1,4),(6,4),(7,4)]
  | 40 => some [(0,5),(1,2),(1,3),(6,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(8,2)]
  | 42 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 43 => some [(2,1),(2,3),(2,5),(4,1),(7,1),(7,5),(8,1)]
  | 44 => some [(0,2),(1,5),(6,0)]
  | 45 => some [(1,1),(6,1),(7,1)]
  | 46 => some [(4,1),(7,5),(8,1)]
  | 47 => some [(0,2),(0,3),(6,0),(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(5,4),(6,5)]
  | 50 => some [(1,2),(3,2),(4,5),(5,2),(5,5),(7,2),(8,2),(8,5)]
  | 51 => some [(4,0),(7,0),(8,0)]
  | 52 => some [(7,3),(8,3)]
  | 53 => some [(4,2),(5,2),(5,5),(8,2),(8,5)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0)]
  | 55 => some [(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 56 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4),(7,4)]
  | 58 => some [(0,5),(1,2),(6,2),(6,3)]
  | 59 => some [(4,4),(7,2),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
theorem root7Node81Domains0_fast_eq : root7Node81Domains0 = expandDomains root7Node81Domains0Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node81Domains0 v = expandDomains root7Node81Domains0Fast v from by decide) v
def root7Node81Domains1 (v : Fin 61) : List State :=
  match v.val with
  | 0 => [(1,5),(5,4),(6,5),(7,5)]
  | 1 => [(0,3),(0,4),(6,1),(6,4)]
  | 2 => [(1,2),(5,1),(5,4)]
  | 3 => [(0,1),(1,4),(6,4),(7,4)]
  | 4 => [(0,5),(1,2),(6,2),(6,3)]
  | 5 => [(4,3)]
  | 6 => [(3,5)]
  | 7 => [(0,3)]
  | 8 => [(4,1)]
  | 9 => [(0,2),(0,3),(1,0),(6,0)]
  | 10 => [(1,1),(7,1),(8,1)]
  | 11 => [(1,4)]
  | 12 => [(0,5)]
  | 13 => [(2,4)]
  | 14 => [(1,3)]
  | 15 => [(5,2)]
  | 16 => [(5,0),(5,3),(8,0)]
  | 17 => [(4,5),(7,3),(8,3),(8,5)]
  | 18 => [(7,5)]
  | 19 => [(6,0)]
  | 20 => [(7,1)]
  | 21 => [(6,5)]
  | 22 => [(0,4)]
  | 23 => [(5,4)]
  | 24 => [(0,0),(1,4),(6,3),(6,4)]
  | 25 => [(0,5),(1,2),(7,2)]
  | 26 => [(7,3)]
  | 27 => [(8,2)]
  | 28 => [(5,0)]
  | 29 => [(4,5)]
  | 30 => [(7,0)]
  | 31 => [(4,3)]
  | 32 => [(7,5)]
  | 33 => [(0,3),(1,1),(6,0),(6,1)]
  | 34 => [(4,1),(7,1),(8,1)]
  | 35 => [(1,2),(6,2)]
  | 36 => [(8,4)]
  | 37 => [(0,0)]
  | 38 => [(7,2)]
  | 39 => [(7,4)]
  | 40 => [(1,3)]
  | 41 => [(2,0),(2,2),(2,4),(4,0),(4,2),(8,2)]
  | 42 => [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 43 => [(7,1),(8,1)]
  | 44 => [(1,5)]
  | 45 => [(6,1)]
  | 46 => [(8,1)]
  | 47 => [(6,5)]
  | 48 => [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => [(0,1),(1,4),(3,4),(5,4),(6,5)]
  | 50 => [(4,5),(5,5),(8,5)]
  | 51 => [(7,0)]
  | 52 => [(8,3)]
  | 53 => [(5,5),(8,5)]
  | 54 => [(3,0),(5,0),(5,3),(7,0)]
  | 55 => [(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 56 => [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 57 => [(0,1),(1,4),(6,4),(7,4)]
  | 58 => [(0,5),(1,2),(6,2),(6,3)]
  | 59 => [(4,4),(7,2),(7,4),(8,4)]
  | _ => [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
def root7Node81Domains1Fast (v : Fin 61) : Option (List State) :=
  match v.val with
  | 0 => some [(1,5),(5,4),(6,5),(7,5)]
  | 1 => some [(0,3),(0,4),(6,1),(6,4)]
  | 2 => some [(1,2),(5,1),(5,4)]
  | 3 => some [(0,1),(1,4),(6,4),(7,4)]
  | 4 => some [(0,5),(1,2),(6,2),(6,3)]
  | 5 => some [(4,3)]
  | 6 => some [(3,5)]
  | 7 => some [(0,3)]
  | 8 => some [(4,1)]
  | 9 => some [(0,2),(0,3),(1,0),(6,0)]
  | 10 => some [(1,1),(7,1),(8,1)]
  | 11 => some [(1,4)]
  | 12 => some [(0,5)]
  | 13 => some [(2,4)]
  | 14 => some [(1,3)]
  | 15 => some [(5,2)]
  | 16 => some [(5,0),(5,3),(8,0)]
  | 17 => some [(4,5),(7,3),(8,3),(8,5)]
  | 18 => some [(7,5)]
  | 19 => some [(6,0)]
  | 20 => some [(7,1)]
  | 21 => some [(6,5)]
  | 22 => some [(0,4)]
  | 23 => some [(5,4)]
  | 24 => some [(0,0),(1,4),(6,3),(6,4)]
  | 25 => some [(0,5),(1,2),(7,2)]
  | 26 => some [(7,3)]
  | 27 => some [(8,2)]
  | 28 => some [(5,0)]
  | 29 => some [(4,5)]
  | 30 => some [(7,0)]
  | 31 => some [(4,3)]
  | 32 => some [(7,5)]
  | 33 => some [(0,3),(1,1),(6,0),(6,1)]
  | 34 => some [(4,1),(7,1),(8,1)]
  | 35 => some [(1,2),(6,2)]
  | 36 => some [(8,4)]
  | 37 => some [(0,0)]
  | 38 => some [(7,2)]
  | 39 => some [(7,4)]
  | 40 => some [(1,3)]
  | 41 => some [(2,0),(2,2),(2,4),(4,0),(4,2),(8,2)]
  | 42 => some [(1,3),(3,3),(5,0),(5,3),(7,3),(8,0)]
  | 43 => some [(7,1),(8,1)]
  | 44 => some [(1,5)]
  | 45 => some [(6,1)]
  | 46 => some [(8,1)]
  | 47 => some [(6,5)]
  | 48 => some [(0,4),(1,1),(3,1),(5,1),(7,1)]
  | 49 => some [(0,1),(1,4),(3,4),(5,4),(6,5)]
  | 50 => some [(4,5),(5,5),(8,5)]
  | 51 => some [(7,0)]
  | 52 => some [(8,3)]
  | 53 => some [(5,5),(8,5)]
  | 54 => some [(3,0),(5,0),(5,3),(7,0)]
  | 55 => some [(2,3),(2,5),(4,3),(4,5),(8,5)]
  | 56 => some [(4,4),(5,1),(5,4),(7,2),(8,4)]
  | 57 => some [(0,1),(1,4),(6,4),(7,4)]
  | 58 => some [(0,5),(1,2),(6,2),(6,3)]
  | 59 => some [(4,4),(7,2),(7,4),(8,4)]
  | _ => some [(0,0),(1,3),(1,4),(6,3),(6,4),(7,4)]
theorem root7Node81Domains1_fast_eq : root7Node81Domains1 = expandDomains root7Node81Domains1Fast := by
  funext v
  exact (show ∀ v : Fin 61, root7Node81Domains1 v = expandDomains root7Node81Domains1Fast v from by decide) v
theorem root7Node81Step1Chunk0_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk0_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk0_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk0_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk0_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk0_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows0_5⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk1_5_checked :
    checkNarrowing ⟨table29Scope, table29Rows1_5⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk2_0_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_0⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk2_1_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_1⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk2_2_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_2⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk2_3_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_3⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
theorem root7Node81Step1Chunk2_4_checked :
    checkNarrowing ⟨table29Scope, table29Rows2_4⟩
      root7Node81Domains0 root7Node81Domains1 = true := by
  exact checkNarrowing_of_fast _ root7Node81Domains0 root7Node81Domains1
    root7Node81Domains0Fast root7Node81Domains1Fast
    root7Node81Domains0_fast_eq root7Node81Domains1_fast_eq (by decide)
end SpectreFinite.HexSearch.RadiusFour
