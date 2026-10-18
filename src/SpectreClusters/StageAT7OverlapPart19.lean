module

public import SpectreClusters.StageAT7OverlapData
public import SpectreClusters.StageAT7OverlapPart18

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000

theorem t7OverlapRefute76 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch76 := by
  apply refute_patch_by_rows hcaptures f hf t7OverlapPatch76 (⟨.hat,4,(1,-3)⟩) (by decide)
  intro i hi
  simp only [keptIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 0) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(2,-3)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro ho
    exact t7OverlapRefute75 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch75 (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 2) (by decide) ho)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 6) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(1,-2)⟩)
      (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 8) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(1,-2)⟩)
      (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 13) (⟨.hat,0,(1,-2)⟩) (⟨.hat,2,(2,-3)⟩)
      (⟨(1,-2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 15) (⟨.hat,0,(1,-2)⟩) (⟨.hat,2,(2,-3)⟩)
      (⟨(1,-2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 16) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(2,-3)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 17) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(2,-3)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 21) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(2,-3)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 22) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(2,-3)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 23) (⟨.hat,1,(0,-2)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 24) (⟨.hat,1,(0,-2)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 27) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(2,-3)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 28) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(2,-3)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 31) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(2,-3)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 32) (⟨.hat,1,(0,-2)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 35) (⟨.hat,0,(0,-4)⟩) (⟨.hat,5,(1,-4)⟩)
      (⟨(1,-5),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 38) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(2,-3)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 39) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(2,-3)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 79) (⟨.hat,0,(0,-4)⟩) (⟨.hat,5,(1,-4)⟩)
      (⟨(1,-5),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 81) (⟨.hat,0,(0,-4)⟩) (⟨.hat,5,(1,-4)⟩)
      (⟨(1,-5),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 89) (⟨.hat,0,(0,-4)⟩) (⟨.hat,5,(1,-4)⟩)
      (⟨(1,-5),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch76 ++ rowPatch (⟨.hat,4,(1,-3)⟩) 210) (⟨.hat,0,(1,-2)⟩) (⟨.turtle,2,(0,-2)⟩)
      (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute77 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch77 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch77) (⟨.hat,0,(1,-2)⟩) (⟨.hat,4,(1,-2)⟩)
    (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

end SpectreClusters.StageA
