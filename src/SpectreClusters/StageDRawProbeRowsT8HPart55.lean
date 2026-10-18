module

public import SpectreClusters.StageDRawOwnedProbes

@[expose] public section

namespace SpectreClusters.StageD.Raw
def probeRowWitnessesT8H55 : List (List Nat × Nat) := [([123,123,249,123,107,148,148,148,251,249,249,251,244,251,251],465),([256,256,249,256,107,148,148,148,251,249,249,251,244,251,251],689),([123,123,249,123,194,148,148,148,251,249,249,251,244,251,251],1061),([256,256,249,256,194,148,148,148,251,249,249,251,244,251,251],1285),([123,123,249,123,239,148,148,148,251,249,249,251,244,251,251],1541),([256,256,249,256,239,148,148,148,251,249,249,251,244,251,251],1765)]
set_option maxRecDepth 100000 in
theorem probeRowWitnessesT8H55_checked : probeRowWitnessesT8H55.all (fun wi => wordCoversRowB .t8h wi.1 wi.2) = true := by rfl
end SpectreClusters.StageD.Raw
