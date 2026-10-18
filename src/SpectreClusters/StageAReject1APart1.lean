module

public import SpectreClusters.StageARejectCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem reject1A_34_slice0 : [0,1,2,3,6,8,10,11,13,15,16,17,21,22,23,24,27,28,31,32,34,35,38,39,79,81,89,91,210,246].all (fun j => !(supportB .hat (rawWordAt .hat 34) 14 (rawWordAt .hat j))) = true := by rfl
theorem reject1A_34_none : noSupportB 1 .hat 34 14 = true := by
  change (keptIds 1 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 34) 14 (rawWordAt .hat j))) = true
  rw [kept1A_partition]
  exact reject1A_34_slice0
set_option maxRecDepth 100000 in
theorem reject1A_34 : rejectionCheckB 1 .hat 34 = true := by
  change (rawWordAt .hat 34).contains 14 && alignmentValidB .hat 14 && noSupportB 1 .hat 34 14 = true
  rw [reject1A_34_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject1A_91_slice0 : [0,1,2,3,6,8,10,11,13,15,16,17,21,22,23,24,27,28,31,32,34,35,38,39,79,81,89,91,210,246].all (fun j => !(supportB .hat (rawWordAt .hat 91) 28 (rawWordAt .hat j))) = true := by rfl
theorem reject1A_91_none : noSupportB 1 .hat 91 28 = true := by
  change (keptIds 1 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 91) 28 (rawWordAt .hat j))) = true
  rw [kept1A_partition]
  exact reject1A_91_slice0
set_option maxRecDepth 100000 in
theorem reject1A_91 : rejectionCheckB 1 .hat 91 = true := by
  change (rawWordAt .hat 91).contains 28 && alignmentValidB .hat 28 && noSupportB 1 .hat 91 28 = true
  rw [reject1A_91_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject1A_246_slice0 : [0,52,163,171,179,183,201,203,205,206,207,208,212,214,215,216,219,221,222,223,226,227,229,231,240,242,244,246,248,250].all (fun j => !(supportB .hat (rawWordAt .hat 246) 40 (rawWordAt .turtle j))) = true := by rfl
theorem reject1A_246_none : noSupportB 1 .hat 246 40 = true := by
  change (keptIds 1 .turtle).all (fun j => !(supportB .hat (rawWordAt .hat 246) 40 (rawWordAt .turtle j))) = true
  rw [kept1B_partition]
  exact reject1A_246_slice0
set_option maxRecDepth 100000 in
theorem reject1A_246 : rejectionCheckB 1 .hat 246 = true := by
  change (rawWordAt .hat 246).contains 40 && alignmentValidB .hat 40 && noSupportB 1 .hat 246 40 = true
  rw [reject1A_246_none]
  rfl
end SpectreClusters.StageA
