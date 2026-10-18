module

public import SpectreClusters.StageDRawReducedCompatibilityModel

@[expose] public section

namespace SpectreClusters.StageD.Raw
def reducedPairWitnessesT8H256 : List (Nat × (Nat × Nat)) := [(16,(0,0)),(23,(0,0)),(28,(0,0)),(30,(0,0)),(37,(0,0)),(40,(0,0)),(45,(0,0)),(48,(0,0)),(55,(38,14)),(85,(0,0)),(90,(0,0)),(95,(0,0)),(100,(38,46)),(104,(0,0)),(107,(0,0)),(114,(0,0)),(116,(0,0)),(118,(0,0)),(123,(38,38)),(137,(0,0)),(144,(38,27)),(148,(0,0)),(155,(0,0)),(162,(0,0)),(168,(0,0)),(172,(0,0)),(177,(0,0)),(180,(0,0)),(187,(38,14)),(191,(0,0)),(194,(0,0)),(206,(0,0)),(217,(20,71)),(228,(0,0)),(232,(38,46)),(236,(0,0)),(239,(0,0)),(244,(0,0)),(249,(0,0)),(251,(0,0)),(256,(0,0))]
set_option maxRecDepth 100000 in
theorem reducedPairWitnessesT8H256_checked : reducedCompatibilityCheck .t8h 256 reducedPairWitnessesT8H256 = true := by rfl
end SpectreClusters.StageD.Raw
