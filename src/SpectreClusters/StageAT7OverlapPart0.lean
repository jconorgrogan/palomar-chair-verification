module

public import SpectreClusters.StageAT7OverlapData

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000

theorem t7OverlapRefute0 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch0 := by
  apply refute_patch_by_rows hcaptures f hf t7OverlapPatch0 (⟨.hat,0,(-2,-1)⟩) (by decide)
  intro i hi
  simp only [keptIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 0) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 2) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 6) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-1,-1)⟩)
      (⟨(-1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 8) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-1,-1)⟩)
      (⟨(-1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 13) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-1,-1)⟩)
      (⟨(-1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 15) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-1,-1)⟩)
      (⟨(-1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 16) (⟨.hat,4,(0,-1)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 17) (⟨.hat,0,(-2,0)⟩) (⟨.hat,4,(-1,0)⟩)
      (⟨(-2,0),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 21) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 22) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 23) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 24) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 27) (⟨.hat,4,(0,-1)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 28) (⟨.hat,0,(-2,0)⟩) (⟨.hat,4,(-1,0)⟩)
      (⟨(-2,0),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 31) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 32) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 35) (⟨.hat,0,(-2,0)⟩) (⟨.hat,4,(-1,0)⟩)
      (⟨(-2,0),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 38) (⟨.hat,4,(0,-1)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 39) (⟨.hat,0,(-2,0)⟩) (⟨.hat,4,(-1,0)⟩)
      (⟨(-2,0),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 79) (⟨.hat,1,(-3,-1)⟩) (⟨.hat,5,(-3,0)⟩)
      (⟨(-3,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 81) (⟨.hat,0,(-2,0)⟩) (⟨.hat,3,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 89) (⟨.hat,2,(0,-2)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch0 ++ rowPatch (⟨.hat,0,(-2,-1)⟩) 210) (⟨.hat,0,(-2,0)⟩) (⟨.turtle,0,(-3,0)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute1 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch1 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch1) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(2,-2)⟩)
    (⟨(2,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute2 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch2 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch2) (⟨.hat,0,(1,0)⟩) (⟨.hat,1,(2,-1)⟩)
    (⟨(2,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute3 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch3 := by
  apply refute_patch_by_rows hcaptures f hf t7OverlapPatch3 (⟨.hat,0,(1,-2)⟩) (by decide)
  intro i hi
  simp only [keptIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 0) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 2) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 6) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(2,-2)⟩)
      (⟨(2,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 8) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(2,-2)⟩)
      (⟨(2,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 13) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(2,-2)⟩)
      (⟨(2,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 15) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(2,-2)⟩)
      (⟨(2,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 16) (⟨.hat,4,(3,-2)⟩) (⟨.hat,5,(3,-2)⟩)
      (⟨(3,-3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 17) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
      (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 21) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 22) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 23) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 24) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 27) (⟨.hat,4,(3,-2)⟩) (⟨.hat,5,(3,-2)⟩)
      (⟨(3,-3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 28) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
      (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 31) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 32) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 35) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
      (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 38) (⟨.hat,4,(3,-2)⟩) (⟨.hat,5,(3,-2)⟩)
      (⟨(3,-3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 39) (⟨.hat,0,(1,-1)⟩) (⟨.hat,4,(2,-1)⟩)
      (⟨(1,-1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 79) (⟨.hat,1,(0,-2)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 81) (⟨.hat,0,(1,-1)⟩) (⟨.hat,3,(1,-1)⟩)
      (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 89) (⟨.hat,2,(3,-3)⟩) (⟨.hat,5,(3,-2)⟩)
      (⟨(3,-3),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch3 ++ rowPatch (⟨.hat,0,(1,-2)⟩) 210) (⟨.hat,0,(1,-1)⟩) (⟨.turtle,0,(0,-1)⟩)
      (⟨(1,-1),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

end SpectreClusters.StageA
