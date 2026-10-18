module

public import SpectreClusters.StageDFinalCoverageModel

@[expose] public section

namespace SpectreClusters.StageD
set_option maxRecDepth 100000 in
theorem row17_pairs_checked :
    (List.finRange 6).all (fun d => (List.finRange 20).all (pairCheckB 17 d)) = true := by rfl
set_option maxRecDepth 100000 in
theorem row17_unique_checked :
    (List.finRange 20).all (uniqueCheckB 17) = true := by rfl
def row17_haloWitnesses : List (Cell × Nat) := [(⟨(0,2),4⟩,4),(⟨(-1,2),0⟩,4),(⟨(-1,2),5⟩,4),(⟨(0,2),3⟩,4),(⟨(0,2),5⟩,4),(⟨(1,1),0⟩,4),(⟨(1,1),1⟩,4),(⟨(-1,2),1⟩,4),(⟨(-1,2),2⟩,4),(⟨(-2,1),5⟩,5),(⟨(-2,2),0⟩,4),(⟨(-2,1),0⟩,5),(⟨(-2,1),4⟩,5),(⟨(-2,2),5⟩,4),(⟨(-1,1),1⟩,5),(⟨(-1,1),2⟩,5),(⟨(-1,-1),0⟩,0),(⟨(-1,-1),1⟩,0),(⟨(-1,0),2⟩,0),(⟨(-1,0),3⟩,0),(⟨(-1,-1),5⟩,0),(⟨(0,-2),1⟩,0),(⟨(0,-2),2⟩,0),(⟨(1,2),4⟩,4),(⟨(1,2),5⟩,4),(⟨(2,1),0⟩,3),(⟨(2,1),4⟩,3),(⟨(2,1),1⟩,3),(⟨(2,1),5⟩,3),(⟨(3,0),2⟩,3),(⟨(3,0),3⟩,3),(⟨(3,-1),0⟩,3),(⟨(3,-1),5⟩,3),(⟨(3,0),4⟩,3),(⟨(2,-2),4⟩,2),(⟨(2,-2),5⟩,2),(⟨(3,-2),1⟩,2),(⟨(3,-2),2⟩,2),(⟨(3,-2),3⟩,2),(⟨(3,-1),3⟩,2),(⟨(3,-1),4⟩,2),(⟨(3,-3),2⟩,1),(⟨(0,-2),3⟩,0),(⟨(1,-3),0⟩,1),(⟨(2,-3),4⟩,1),(⟨(0,-2),4⟩,0),(⟨(1,-3),1⟩,0),(⟨(1,-3),2⟩,0),(⟨(2,-3),2⟩,1),(⟨(2,-3),3⟩,1),(⟨(2,-3),5⟩,1),(⟨(3,-3),3⟩,1)]
set_option maxRecDepth 100000 in
theorem row17_basics_checked : rowBasicsB 17 = true := by
  apply rowBasics_of_witness 17 row17_haloWitnesses
  · rfl
  · rfl
  · rfl
end SpectreClusters.StageD
