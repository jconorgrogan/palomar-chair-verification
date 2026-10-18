module

public import SpectreClusters.StageAT7OverlapData
public import SpectreClusters.StageAT7OverlapPart9

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000

theorem t7OverlapRefute40 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch40 := by
  apply refute_patch_by_rows hcaptures f hf t7OverlapPatch40 (⟨.hat,2,(1,0)⟩) (by decide)
  intro i hi
  simp only [keptIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 0) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 2) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
      (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 6) (⟨.hat,0,(1,-1)⟩) (⟨.turtle,2,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 8) (⟨.hat,0,(0,2)⟩) (⟨.hat,1,(0,2)⟩)
      (⟨(0,2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 13) (⟨.hat,1,(0,2)⟩) (⟨.hat,4,(1,2)⟩)
      (⟨(0,2),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 15) (⟨.hat,0,(0,2)⟩) (⟨.hat,1,(0,2)⟩)
      (⟨(0,2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 16) (⟨.hat,0,(-1,2)⟩) (⟨.hat,3,(0,1)⟩)
      (⟨(-1,2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 17) (⟨.hat,0,(-1,1)⟩) (⟨.hat,1,(-1,0)⟩)
      (⟨(-1,1),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 21) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 22) (⟨.hat,0,(0,2)⟩) (⟨.hat,1,(0,2)⟩)
      (⟨(0,2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 23) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
      (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 24) (⟨.hat,0,(0,2)⟩) (⟨.hat,1,(0,2)⟩)
      (⟨(0,2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 27) (⟨.hat,0,(-1,2)⟩) (⟨.hat,3,(0,1)⟩)
      (⟨(-1,2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 28) (⟨.hat,0,(-1,1)⟩) (⟨.hat,1,(-1,0)⟩)
      (⟨(-1,1),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 31) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 32) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
      (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 35) (⟨.hat,0,(-1,1)⟩) (⟨.hat,1,(-1,0)⟩)
      (⟨(-1,1),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 38) (⟨.hat,0,(-1,2)⟩) (⟨.hat,3,(0,1)⟩)
      (⟨(-1,2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 39) (⟨.hat,0,(-1,1)⟩) (⟨.hat,1,(-1,0)⟩)
      (⟨(-1,1),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 79) (⟨.hat,0,(1,-1)⟩) (⟨.hat,3,(2,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 81) (⟨.hat,0,(-1,1)⟩) (⟨.hat,1,(-1,0)⟩)
      (⟨(-1,1),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 89) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch40 ++ rowPatch (⟨.hat,2,(1,0)⟩) 210) (⟨.hat,0,(1,-1)⟩) (⟨.turtle,2,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute41 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch41 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch41) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(1,-2)⟩)
    (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute42 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch42 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch42) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(2,-2)⟩)
    (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute43 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch43 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch43) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
    (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

end SpectreClusters.StageA
