module

public import SpectreClusters.StageARejectCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem reject1B_208_slice0 : [0,52,163,171,179,183,201,203,205,206,207,208,212,214,215,216,219,221,222,223,226,227,229,231,240,242,244,246,248,250].all (fun j => !(supportB .turtle (rawWordAt .turtle 208) 26 (rawWordAt .turtle j))) = true := by rfl
theorem reject1B_208_none : noSupportB 1 .turtle 208 26 = true := by
  change (keptIds 1 .turtle).all (fun j => !(supportB .turtle (rawWordAt .turtle 208) 26 (rawWordAt .turtle j))) = true
  rw [kept1B_partition]
  exact reject1B_208_slice0
set_option maxRecDepth 100000 in
theorem reject1B_208 : rejectionCheckB 1 .turtle 208 = true := by
  change (rawWordAt .turtle 208).contains 26 && alignmentValidB .turtle 26 && noSupportB 1 .turtle 208 26 = true
  rw [reject1B_208_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject1B_216_slice0 : [0,52,163,171,179,183,201,203,205,206,207,208,212,214,215,216,219,221,222,223,226,227,229,231,240,242,244,246,248,250].all (fun j => !(supportB .turtle (rawWordAt .turtle 216) 29 (rawWordAt .turtle j))) = true := by rfl
theorem reject1B_216_none : noSupportB 1 .turtle 216 29 = true := by
  change (keptIds 1 .turtle).all (fun j => !(supportB .turtle (rawWordAt .turtle 216) 29 (rawWordAt .turtle j))) = true
  rw [kept1B_partition]
  exact reject1B_216_slice0
set_option maxRecDepth 100000 in
theorem reject1B_216 : rejectionCheckB 1 .turtle 216 = true := by
  change (rawWordAt .turtle 216).contains 29 && alignmentValidB .turtle 29 && noSupportB 1 .turtle 216 29 = true
  rw [reject1B_216_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject1B_244_slice0 : [0,52,163,171,179,183,201,203,205,206,207,208,212,214,215,216,219,221,222,223,226,227,229,231,240,242,244,246,248,250].all (fun j => !(supportB .turtle (rawWordAt .turtle 244) 41 (rawWordAt .turtle j))) = true := by rfl
theorem reject1B_244_none : noSupportB 1 .turtle 244 41 = true := by
  change (keptIds 1 .turtle).all (fun j => !(supportB .turtle (rawWordAt .turtle 244) 41 (rawWordAt .turtle j))) = true
  rw [kept1B_partition]
  exact reject1B_244_slice0
set_option maxRecDepth 100000 in
theorem reject1B_244 : rejectionCheckB 1 .turtle 244 = true := by
  change (rawWordAt .turtle 244).contains 41 && alignmentValidB .turtle 41 && noSupportB 1 .turtle 244 41 = true
  rw [reject1B_244_none]
  rfl
end SpectreClusters.StageA
