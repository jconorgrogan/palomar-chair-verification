module

public import SpectreClusters.StageAT7OverlapData
public import SpectreClusters.StageAT7OverlapPart8

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000

theorem t7OverlapRefute36 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch36 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch36) (⟨.hat,1,(-1,0)⟩) (⟨.hat,2,(0,-1)⟩)
    (⟨(-1,0),4⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute37 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch37 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch37) (⟨.hat,0,(1,-2)⟩) (⟨.hat,0,(2,-2)⟩)
    (⟨(2,-2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute38 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch38 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch38) (⟨.hat,0,(2,0)⟩) (⟨.hat,1,(2,-1)⟩)
    (⟨(2,0),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute39 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch39 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch39) (⟨.hat,2,(-1,1)⟩) (⟨.hat,3,(0,1)⟩)
    (⟨(-1,1),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

end SpectreClusters.StageA
