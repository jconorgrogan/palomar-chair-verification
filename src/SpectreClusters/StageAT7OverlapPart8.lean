module

public import SpectreClusters.StageAT7OverlapData
public import SpectreClusters.StageAT7OverlapPart7

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000

theorem t7OverlapRefute32 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch32 := by
  apply refute_patch_by_rows hcaptures f hf t7OverlapPatch32 (⟨.hat,5,(-1,-1)⟩) (by decide)
  intro i hi
  simp only [keptIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 0) (⟨.hat,0,(-3,0)⟩) (⟨.hat,0,(-2,0)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 2) (⟨.hat,0,(-3,0)⟩) (⟨.hat,0,(-2,0)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 6) (⟨.hat,0,(-2,0)⟩) (⟨.hat,4,(-2,0)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 8) (⟨.hat,0,(-2,0)⟩) (⟨.hat,4,(-2,0)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 13) (⟨.hat,0,(-2,0)⟩) (⟨.hat,3,(-1,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 15) (⟨.hat,0,(-2,0)⟩) (⟨.hat,3,(-1,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 16) (⟨.hat,0,(-3,0)⟩) (⟨.hat,0,(-2,0)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 17) (⟨.hat,0,(-3,0)⟩) (⟨.hat,0,(-2,0)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 21) (⟨.hat,0,(-2,0)⟩) (⟨.hat,2,(-2,-1)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 22) (⟨.hat,0,(-2,0)⟩) (⟨.hat,2,(-2,-1)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 23) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 24) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 27) (⟨.hat,0,(-2,0)⟩) (⟨.hat,2,(-2,-1)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 28) (⟨.hat,0,(-2,0)⟩) (⟨.hat,2,(-2,-1)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 31) (⟨.hat,0,(-2,0)⟩) (⟨.hat,2,(-2,-1)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 32) (⟨.hat,0,(-2,0)⟩) (⟨.hat,1,(-2,0)⟩)
      (⟨(-2,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 35) (⟨.hat,0,(-2,0)⟩) (⟨.hat,2,(-2,-1)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 38) (⟨.hat,0,(-2,0)⟩) (⟨.hat,2,(-2,-1)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 39) (⟨.hat,0,(-2,0)⟩) (⟨.hat,2,(-2,-1)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro ho
    exact t7OverlapRefute31 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch31 (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 79) (by decide) ho)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 81) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(1,-2)⟩)
      (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 89) (⟨.hat,0,(-2,0)⟩) (⟨.hat,4,(-1,0)⟩)
      (⟨(-2,0),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch32 ++ rowPatch (⟨.hat,5,(-1,-1)⟩) 210) (⟨.hat,0,(-2,0)⟩) (⟨.turtle,3,(-2,-1)⟩)
      (⟨(-2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute33 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch33 := by
  apply refute_patch_by_rows hcaptures f hf t7OverlapPatch33 (⟨.hat,0,(-2,0)⟩) (by decide)
  intro i hi
  simp only [keptIds,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 0) (⟨.hat,2,(-3,0)⟩) (⟨.hat,5,(-3,1)⟩)
      (⟨(-3,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 2) (⟨.hat,2,(0,-2)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 6) (⟨.hat,1,(-2,1)⟩) (⟨.hat,2,(-2,1)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 8) (⟨.hat,1,(-2,1)⟩) (⟨.hat,2,(-2,1)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 13) (⟨.hat,1,(-2,1)⟩) (⟨.hat,5,(-2,2)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 15) (⟨.hat,1,(-2,1)⟩) (⟨.hat,5,(-2,2)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 16) (⟨.hat,0,(-2,1)⟩) (⟨.hat,1,(-2,1)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 17) (⟨.hat,1,(-2,1)⟩) (⟨.hat,4,(-1,1)⟩)
      (⟨(-2,1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 21) (⟨.hat,2,(-3,0)⟩) (⟨.hat,5,(-3,1)⟩)
      (⟨(-3,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 22) (⟨.hat,2,(-3,0)⟩) (⟨.hat,5,(-3,1)⟩)
      (⟨(-3,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 23) (⟨.hat,2,(0,-2)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 24) (⟨.hat,4,(0,-1)⟩) (⟨.hat,5,(0,-1)⟩)
      (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 27) (⟨.hat,0,(-2,1)⟩) (⟨.hat,1,(-2,1)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 28) (⟨.hat,1,(-2,1)⟩) (⟨.hat,4,(-1,1)⟩)
      (⟨(-2,1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 31) (⟨.hat,2,(-3,0)⟩) (⟨.hat,5,(-3,1)⟩)
      (⟨(-3,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro ho
    exact t7OverlapRefute32 hcaptures f hf
      (patchOwned_of_subpatch f t7OverlapPatch32 (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 32) (by decide) ho)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 35) (⟨.hat,0,(1,-2)⟩) (⟨.hat,3,(1,-2)⟩)
      (⟨(1,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 38) (⟨.hat,0,(-2,1)⟩) (⟨.hat,1,(-2,1)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 39) (⟨.hat,1,(-2,1)⟩) (⟨.hat,4,(-1,1)⟩)
      (⟨(-2,1),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 79) (⟨.hat,0,(-2,1)⟩) (⟨.hat,1,(-2,1)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 81) (⟨.hat,1,(-3,0)⟩) (⟨.hat,2,(-3,0)⟩)
      (⟨(-3,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 89) (⟨.hat,0,(-2,1)⟩) (⟨.hat,1,(-2,1)⟩)
      (⟨(-2,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact patch_not_owned_of_collision f (t7OverlapPatch33 ++ rowPatch (⟨.hat,0,(-2,0)⟩) 210) (⟨.hat,0,(1,-1)⟩) (⟨.turtle,0,(0,-1)⟩)
      (⟨(1,-1),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute34 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch34 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch34) (⟨.hat,0,(-1,-1)⟩) (⟨.hat,5,(0,-1)⟩)
    (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute35 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch35 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch35) (⟨.hat,0,(1,-1)⟩) (⟨.hat,1,(1,-1)⟩)
    (⟨(1,-1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

end SpectreClusters.StageA
