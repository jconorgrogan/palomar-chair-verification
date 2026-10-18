module

public import SpectreClusters.StageAT7OverlapData
public import SpectreClusters.StageAT7OverlapPart11

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000

theorem t7OverlapRefute48 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch48 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch48) (⟨.hat,1,(-1,0)⟩) (⟨.hat,4,(-1,1)⟩)
    (⟨(-1,0),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute49 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch49 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch49) (⟨.hat,0,(-1,-1)⟩) (⟨.hat,5,(0,-1)⟩)
    (⟨(0,-2),0⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute50 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch50 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch50) (⟨.hat,0,(-1,1)⟩) (⟨.hat,1,(-1,0)⟩)
    (⟨(-1,1),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem t7OverlapRefute51 (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) :
    ¬PatchOwned f t7OverlapPatch51 := by
  exact patch_not_owned_of_collision f (t7OverlapPatch51) (⟨.hat,0,(-1,2)⟩) (⟨.hat,3,(0,1)⟩)
    (⟨(-1,2),3⟩) (by decide) (by decide) (by decide) (by decide) (by decide)

end SpectreClusters.StageA
