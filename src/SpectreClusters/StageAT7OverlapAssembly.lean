module

public import SpectreClusters.StageAT7OverlapPart19
public import SpectreClusters.StageAT7Alignment

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000
def t7PairPatch (other : HTPlacement) : List HTPlacement :=
  clusterPieces .t7h ++ clusterPiecesAt .t7h other

theorem t7_other_roots_refuted (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (other : HTPlacement)
    (hother : other ∈ t7SharedOtherRoots) : ¬PatchOwned f (t7PairPatch other) := by
  simp only [t7SharedOtherRoots,List.mem_cons,List.not_mem_nil,or_false] at hother
  rcases hother with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro ho
    exact t7OverlapRefute0 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch0 (t7PairPatch (⟨.turtle,0,(-3,1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute1 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch1 (t7PairPatch (⟨.turtle,0,(0,-1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute2 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch2 (t7PairPatch (⟨.turtle,0,(0,1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute3 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch3 (t7PairPatch (⟨.turtle,0,(3,-1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute33 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch33 (t7PairPatch (⟨.turtle,1,(-3,1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute34 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch34 (t7PairPatch (⟨.turtle,1,(-2,0)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute35 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch35 (t7PairPatch (⟨.turtle,1,(0,-1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute36 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch36 (t7PairPatch (⟨.turtle,1,(0,0)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute37 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch37 (t7PairPatch (⟨.turtle,1,(1,-1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute38 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch38 (t7PairPatch (⟨.turtle,1,(1,1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute39 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch39 (t7PairPatch (⟨.turtle,2,(-2,0)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute40 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch40 (t7PairPatch (⟨.turtle,2,(-1,2)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute41 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch41 (t7PairPatch (⟨.turtle,2,(0,-1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute42 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch42 (t7PairPatch (⟨.turtle,2,(1,-1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute43 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch43 (t7PairPatch (⟨.turtle,3,(1,-1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute44 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch44 (t7PairPatch (⟨.turtle,3,(1,0)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute45 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch45 (t7PairPatch (⟨.turtle,4,(-2,1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute46 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch46 (t7PairPatch (⟨.turtle,4,(0,-2)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute47 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch47 (t7PairPatch (⟨.turtle,4,(1,-1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute48 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch48 (t7PairPatch (⟨.turtle,4,(1,0)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute49 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch49 (t7PairPatch (⟨.turtle,5,(-2,1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute50 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch50 (t7PairPatch (⟨.turtle,5,(0,0)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute51 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch51 (t7PairPatch (⟨.turtle,5,(0,1)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute52 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch52 (t7PairPatch (⟨.turtle,5,(1,0)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute76 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch76 (t7PairPatch (⟨.turtle,5,(2,-3)⟩)) (by decide) ho)
  · intro ho
    exact t7OverlapRefute77 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch77 (t7PairPatch (⟨.turtle,5,(2,-2)⟩)) (by decide) ho)

end SpectreClusters.StageA
