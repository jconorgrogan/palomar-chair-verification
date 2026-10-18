module

public import SpectreClusters.StageAT7OverlapData
public import SpectreClusters.StageAT7OverlapPart10

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000

theorem t7OverlapRefute44 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch44 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch44) (⟨.hat,1,(-1,0)⟩) (⟨.hat,4,(-1,1)⟩)
    (⟨(-1,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute45 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch45 := by
  apply refute_patch_by_rows hcaptures f hf t7OverlapPatch45 (⟨.hat,0,(-2,0)⟩) (by decide)
  intro i hi
  simp only [keptIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 0) (⟨.hat,1,(-3,-1)⟩) (⟨.hat,5,(-3,0)⟩)
      (⟨(-3,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 2) (⟨.hat,1,(-3,-1)⟩) (⟨.hat,5,(-3,0)⟩)
      (⟨(-3,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 6) (⟨.hat,2,(-2,1)⟩) (⟨.hat,5,(-2,2)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 8) (⟨.hat,2,(-2,1)⟩) (⟨.hat,5,(-2,2)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 13) (⟨.hat,2,(0,-2)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 15) (⟨.hat,4,(0,-1)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 16) (⟨.hat,0,(-2,1)⟩) (⟨.hat,1,(-1,0)⟩)
      (⟨(-1,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 17) (⟨.hat,1,(-3,-1)⟩) (⟨.hat,5,(-3,0)⟩)
      (⟨(-3,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 21) (⟨.hat,1,(-2,1)⟩) (⟨.hat,5,(-2,2)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 22) (⟨.hat,1,(-2,1)⟩) (⟨.hat,5,(-2,2)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 23) (⟨.hat,1,(-2,1)⟩) (⟨.hat,5,(-2,2)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 24) (⟨.hat,1,(-2,1)⟩) (⟨.hat,5,(-2,2)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 27) (⟨.hat,0,(-2,1)⟩) (⟨.hat,1,(-1,0)⟩)
      (⟨(-1,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 28) (⟨.hat,1,(-1,0)⟩) (⟨.hat,4,(-1,1)⟩)
      (⟨(-1,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 31) (⟨.hat,1,(-2,1)⟩) (⟨.hat,5,(-2,2)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 32) (⟨.hat,1,(-2,1)⟩) (⟨.hat,5,(-2,2)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 35) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(1,-2)⟩)
      (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 38) (⟨.hat,0,(-2,1)⟩) (⟨.hat,1,(-1,0)⟩)
      (⟨(-1,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 39) (⟨.hat,1,(-1,0)⟩) (⟨.hat,4,(-1,1)⟩)
      (⟨(-1,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 79) (⟨.hat,0,(-2,1)⟩) (⟨.hat,1,(-1,0)⟩)
      (⟨(-1,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 81) (⟨.hat,1,(-3,0)⟩) (⟨.hat,4,(-3,1)⟩)
      (⟨(-3,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 89) (⟨.hat,0,(-2,1)⟩) (⟨.hat,1,(-1,0)⟩)
      (⟨(-1,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch45 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 210) (⟨.hat,0,(1,-1)⟩) (⟨.turtle,0,(0,-1)⟩)
      (⟨(1,-1),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute46 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch46 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch46) (⟨.hat,0,(1,-2)⟩) (⟨.hat,1,(1,-3)⟩)
    (⟨(1,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute47 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch47 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch47) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(2,-2)⟩)
    (⟨(2,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

end SpectreClusters.StageA
