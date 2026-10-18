module

public import SpectreClusters.StageAT7OverlapData
public import SpectreClusters.StageAT7OverlapPart4

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000

theorem t7OverlapRefute20 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch20 := by
  apply refute_patch_by_rows hcaptures f hf t7OverlapPatch20 (⟨.hat,3,(-3,2)⟩) (by decide)
  intro i hi
  simp only [keptIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 0) (⟨.hat,0,(-2,0)⟩) (⟨.turtle,2,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 2) (⟨.hat,1,(-2,1)⟩) (⟨.hat,5,(-2,2)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 6) (⟨.hat,1,(-2,1)⟩) (⟨.turtle,3,(-2,1)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 8) (⟨.hat,1,(-2,1)⟩) (⟨.turtle,3,(-2,1)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro ho
    exact t7OverlapRefute5 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch5 (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 13) (by decide) ho)
  · intro ho
    exact t7OverlapRefute19 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch19 (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 15) (by decide) ho)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 16) (⟨.hat,1,(-5,2)⟩) (⟨.hat,4,(-4,2)⟩)
      (⟨(-5,2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 17) (⟨.hat,1,(-5,2)⟩) (⟨.hat,4,(-4,2)⟩)
      (⟨(-5,2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 21) (⟨.hat,0,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 22) (⟨.hat,0,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 23) (⟨.hat,0,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 24) (⟨.hat,0,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 27) (⟨.hat,0,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 28) (⟨.hat,0,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 31) (⟨.hat,0,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 32) (⟨.hat,0,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 35) (⟨.hat,0,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 38) (⟨.hat,0,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 39) (⟨.hat,0,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 79) (⟨.hat,1,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 81) (⟨.hat,0,(-3,1)⟩) (⟨.hat,0,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 89) (⟨.hat,1,(-3,3)⟩) (⟨.hat,2,(-2,2)⟩)
      (⟨(-3,3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch20 ++ rowPatch (⟨.hat,3,(-3,2)⟩) 210) (⟨.hat,0,(-2,0)⟩) (⟨.turtle,5,(-3,1)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute21 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch21 := by
  apply refute_patch_by_rows hcaptures f hf t7OverlapPatch21 (⟨.hat,1,(1,2)⟩) (by decide)
  intro i hi
  simp only [keptIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 0) (⟨.hat,1,(0,3)⟩) (⟨.hat,2,(0,3)⟩)
      (⟨(0,3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 2) (⟨.hat,0,(0,2)⟩) (⟨.hat,3,(1,1)⟩)
      (⟨(0,2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 6) (⟨.hat,0,(0,2)⟩) (⟨.hat,0,(1,1)⟩)
      (⟨(1,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 8) (⟨.hat,0,(0,2)⟩) (⟨.hat,0,(1,1)⟩)
      (⟨(1,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 13) (⟨.hat,0,(-1,4)⟩) (⟨.hat,1,(0,3)⟩)
      (⟨(0,3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 15) (⟨.hat,0,(-1,4)⟩) (⟨.hat,1,(0,3)⟩)
      (⟨(0,3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro ho
    exact t7OverlapRefute20 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch20 (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 16) (by decide) ho)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 17) (⟨.hat,1,(0,3)⟩) (⟨.hat,5,(0,4)⟩)
      (⟨(0,3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 21) (⟨.hat,1,(0,3)⟩) (⟨.hat,2,(0,3)⟩)
      (⟨(0,3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 22) (⟨.hat,1,(0,3)⟩) (⟨.hat,2,(0,3)⟩)
      (⟨(0,3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 23) (⟨.hat,0,(0,2)⟩) (⟨.hat,3,(1,1)⟩)
      (⟨(0,2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 24) (⟨.hat,0,(0,2)⟩) (⟨.hat,3,(1,1)⟩)
      (⟨(0,2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 27) (⟨.hat,2,(2,0)⟩) (⟨.hat,4,(2,1)⟩)
      (⟨(1,1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 28) (⟨.hat,1,(0,3)⟩) (⟨.hat,5,(0,4)⟩)
      (⟨(0,3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 31) (⟨.hat,1,(0,3)⟩) (⟨.hat,2,(0,3)⟩)
      (⟨(0,3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 32) (⟨.hat,0,(0,2)⟩) (⟨.hat,3,(1,1)⟩)
      (⟨(0,2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 35) (⟨.hat,1,(0,3)⟩) (⟨.hat,5,(0,4)⟩)
      (⟨(0,3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 38) (⟨.hat,2,(2,0)⟩) (⟨.hat,4,(2,1)⟩)
      (⟨(1,1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 39) (⟨.hat,1,(0,3)⟩) (⟨.hat,5,(0,4)⟩)
      (⟨(0,3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 79) (⟨.hat,0,(0,2)⟩) (⟨.hat,2,(1,1)⟩)
      (⟨(0,2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 81) (⟨.hat,0,(0,2)⟩) (⟨.hat,2,(1,1)⟩)
      (⟨(0,2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 89) (⟨.hat,2,(2,0)⟩) (⟨.hat,5,(2,1)⟩)
      (⟨(2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch21 ++ rowPatch (⟨.hat,1,(1,2)⟩) 210) (⟨.hat,0,(0,2)⟩) (⟨.turtle,1,(0,2)⟩)
      (⟨(0,2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute22 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch22 := by
  apply refute_patch_by_rows hcaptures f hf t7OverlapPatch22 (⟨.hat,0,(1,-2)⟩) (by decide)
  intro i hi
  simp only [keptIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 0) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 2) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 6) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(2,-2)⟩)
      (⟨(2,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 8) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(2,-2)⟩)
      (⟨(2,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 13) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(2,-2)⟩)
      (⟨(2,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 15) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(2,-2)⟩)
      (⟨(2,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro ho
    exact t7OverlapRefute21 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch21 (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 16) (by decide) ho)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 17) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
      (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 21) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 22) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 23) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 24) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 27) (⟨.hat,1,(0,-3)⟩) (⟨.hat,3,(1,-3)⟩)
      (⟨(0,-3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 28) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
      (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 31) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 32) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 35) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
      (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 38) (⟨.hat,1,(0,-3)⟩) (⟨.hat,3,(1,-3)⟩)
      (⟨(0,-3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 39) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
      (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 79) (⟨.hat,1,(0,-3)⟩) (⟨.hat,1,(0,-2)⟩)
      (⟨(0,-2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 81) (⟨.hat,0,(1,-1)⟩) (⟨.hat,3,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 89) (⟨.hat,1,(0,-3)⟩) (⟨.hat,4,(1,-3)⟩)
      (⟨(0,-3),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch22 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 210) (⟨.hat,0,(1,-1)⟩) (⟨.turtle,0,(0,-1)⟩)
      (⟨(1,-1),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute23 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch23 := by
  apply refute_patch_by_rows hcaptures f hf t7OverlapPatch23 (⟨.hat,0,(1,-1)⟩) (by decide)
  intro i hi
  simp only [keptIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 0) (⟨.hat,1,(-1,0)⟩) (⟨.hat,5,(0,0)⟩)
      (⟨(0,0),2⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 2) (⟨.hat,1,(-1,0)⟩) (⟨.hat,2,(0,-1)⟩)
      (⟨(-1,0),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro ho
    exact t7OverlapRefute4 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch4 (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 6) (by decide) ho)
  · intro ho
    exact t7OverlapRefute22 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch22 (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 8) (by decide) ho)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 13) (⟨.hat,1,(-1,0)⟩) (⟨.hat,4,(0,0)⟩)
      (⟨(-1,0),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 15) (⟨.hat,1,(-1,0)⟩) (⟨.hat,4,(0,0)⟩)
      (⟨(-1,0),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 16) (⟨.hat,0,(1,0)⟩) (⟨.hat,1,(2,-1)⟩)
      (⟨(2,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 17) (⟨.hat,1,(-1,0)⟩) (⟨.hat,5,(0,0)⟩)
      (⟨(0,0),2⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 21) (⟨.hat,0,(1,-2)⟩) (⟨.hat,2,(2,-3)⟩)
      (⟨(1,-2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 22) (⟨.hat,0,(1,-2)⟩) (⟨.hat,2,(2,-3)⟩)
      (⟨(1,-2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 23) (⟨.hat,0,(1,-2)⟩) (⟨.hat,2,(2,-3)⟩)
      (⟨(1,-2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 24) (⟨.hat,0,(1,-2)⟩) (⟨.hat,2,(2,-3)⟩)
      (⟨(1,-2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 27) (⟨.hat,0,(1,-2)⟩) (⟨.hat,2,(2,-3)⟩)
      (⟨(1,-2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 28) (⟨.hat,0,(1,-2)⟩) (⟨.hat,2,(2,-3)⟩)
      (⟨(1,-2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 31) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(1,-2)⟩)
      (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 32) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(1,-2)⟩)
      (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 35) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(1,-2)⟩)
      (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 38) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(1,-2)⟩)
      (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 39) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(1,-2)⟩)
      (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 79) (⟨.hat,0,(1,-2)⟩) (⟨.hat,4,(1,-2)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 81) (⟨.hat,0,(1,-2)⟩) (⟨.hat,4,(1,-2)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 89) (⟨.hat,0,(1,-2)⟩) (⟨.hat,4,(1,-2)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch23 ++ rowPatch (⟨.hat,0,(1,-1)⟩) 210) (⟨.hat,0,(1,-2)⟩) (⟨.turtle,4,(1,-2)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

end SpectreClusters.StageA
