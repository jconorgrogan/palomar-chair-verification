module

public import SpectreClusters.StageARejectCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem reject1B_52_slice0 : [0,1,2,3,6,8,10,11,13,15,16,17,21,22,23,24,27,28,31,32,34,35,38,39,79,81,89,91,210,246].all (fun j => !(supportB .turtle (rawWordAt .turtle 52) 11 (rawWordAt .hat j))) = true := by rfl
theorem reject1B_52_none : noSupportB 1 .turtle 52 11 = true := by
  change (keptIds 1 .hat).all (fun j => !(supportB .turtle (rawWordAt .turtle 52) 11 (rawWordAt .hat j))) = true
  rw [kept1A_partition]
  exact reject1B_52_slice0
set_option maxRecDepth 100000 in
theorem reject1B_52 : rejectionCheckB 1 .turtle 52 = true := by
  change (rawWordAt .turtle 52).contains 11 && alignmentValidB .turtle 11 && noSupportB 1 .turtle 52 11 = true
  rw [reject1B_52_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject1B_183_slice0 : [0,52,163,171,179,183,201,203,205,206,207,208,212,214,215,216,219,221,222,223,226,227,229,231,240,242,244,246,248,250].all (fun j => !(supportB .turtle (rawWordAt .turtle 183) 58 (rawWordAt .turtle j))) = true := by rfl
theorem reject1B_183_none : noSupportB 1 .turtle 183 58 = true := by
  change (keptIds 1 .turtle).all (fun j => !(supportB .turtle (rawWordAt .turtle 183) 58 (rawWordAt .turtle j))) = true
  rw [kept1B_partition]
  exact reject1B_183_slice0
set_option maxRecDepth 100000 in
theorem reject1B_183 : rejectionCheckB 1 .turtle 183 = true := by
  change (rawWordAt .turtle 183).contains 58 && alignmentValidB .turtle 58 && noSupportB 1 .turtle 183 58 = true
  rw [reject1B_183_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject1B_206_slice0 : [0,52,163,171,179,183,201,203,205,206,207,208,212,214,215,216,219,221,222,223,226,227,229,231,240,242,244,246,248,250].all (fun j => !(supportB .turtle (rawWordAt .turtle 206) 29 (rawWordAt .turtle j))) = true := by rfl
theorem reject1B_206_none : noSupportB 1 .turtle 206 29 = true := by
  change (keptIds 1 .turtle).all (fun j => !(supportB .turtle (rawWordAt .turtle 206) 29 (rawWordAt .turtle j))) = true
  rw [kept1B_partition]
  exact reject1B_206_slice0
set_option maxRecDepth 100000 in
theorem reject1B_206 : rejectionCheckB 1 .turtle 206 = true := by
  change (rawWordAt .turtle 206).contains 29 && alignmentValidB .turtle 29 && noSupportB 1 .turtle 206 29 = true
  rw [reject1B_206_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject1B_207_slice0 : [0,52,163,171,179,183,201,203,205,206,207,208,212,214,215,216,219,221,222,223,226,227,229,231,240,242,244,246,248,250].all (fun j => !(supportB .turtle (rawWordAt .turtle 207) 26 (rawWordAt .turtle j))) = true := by rfl
theorem reject1B_207_none : noSupportB 1 .turtle 207 26 = true := by
  change (keptIds 1 .turtle).all (fun j => !(supportB .turtle (rawWordAt .turtle 207) 26 (rawWordAt .turtle j))) = true
  rw [kept1B_partition]
  exact reject1B_207_slice0
set_option maxRecDepth 100000 in
theorem reject1B_207 : rejectionCheckB 1 .turtle 207 = true := by
  change (rawWordAt .turtle 207).contains 26 && alignmentValidB .turtle 26 && noSupportB 1 .turtle 207 26 = true
  rw [reject1B_207_none]
  rfl
end SpectreClusters.StageA
