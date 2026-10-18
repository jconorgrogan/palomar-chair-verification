module

public import SpectreClusters.StageARejectCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem reject1A_1_slice0 : [0,1,2,3,6,8,10,11,13,15,16,17,21,22,23,24,27,28,31,32,34,35,38,39,79,81,89,91,210,246].all (fun j => !(supportB .hat (rawWordAt .hat 1) 1 (rawWordAt .hat j))) = true := by rfl
theorem reject1A_1_none : noSupportB 1 .hat 1 1 = true := by
  change (keptIds 1 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 1) 1 (rawWordAt .hat j))) = true
  rw [kept1A_partition]
  exact reject1A_1_slice0
set_option maxRecDepth 100000 in
theorem reject1A_1 : rejectionCheckB 1 .hat 1 = true := by
  change (rawWordAt .hat 1).contains 1 && alignmentValidB .hat 1 && noSupportB 1 .hat 1 1 = true
  rw [reject1A_1_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject1A_3_slice0 : [0,1,2,3,6,8,10,11,13,15,16,17,21,22,23,24,27,28,31,32,34,35,38,39,79,81,89,91,210,246].all (fun j => !(supportB .hat (rawWordAt .hat 3) 1 (rawWordAt .hat j))) = true := by rfl
theorem reject1A_3_none : noSupportB 1 .hat 3 1 = true := by
  change (keptIds 1 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 3) 1 (rawWordAt .hat j))) = true
  rw [kept1A_partition]
  exact reject1A_3_slice0
set_option maxRecDepth 100000 in
theorem reject1A_3 : rejectionCheckB 1 .hat 3 = true := by
  change (rawWordAt .hat 3).contains 1 && alignmentValidB .hat 1 && noSupportB 1 .hat 3 1 = true
  rw [reject1A_3_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject1A_10_slice0 : [0,1,2,3,6,8,10,11,13,15,16,17,21,22,23,24,27,28,31,32,34,35,38,39,79,81,89,91,210,246].all (fun j => !(supportB .hat (rawWordAt .hat 10) 0 (rawWordAt .hat j))) = true := by rfl
theorem reject1A_10_none : noSupportB 1 .hat 10 0 = true := by
  change (keptIds 1 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 10) 0 (rawWordAt .hat j))) = true
  rw [kept1A_partition]
  exact reject1A_10_slice0
set_option maxRecDepth 100000 in
theorem reject1A_10 : rejectionCheckB 1 .hat 10 = true := by
  change (rawWordAt .hat 10).contains 0 && alignmentValidB .hat 0 && noSupportB 1 .hat 10 0 = true
  rw [reject1A_10_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject1A_11_slice0 : [0,1,2,3,6,8,10,11,13,15,16,17,21,22,23,24,27,28,31,32,34,35,38,39,79,81,89,91,210,246].all (fun j => !(supportB .hat (rawWordAt .hat 11) 0 (rawWordAt .hat j))) = true := by rfl
theorem reject1A_11_none : noSupportB 1 .hat 11 0 = true := by
  change (keptIds 1 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 11) 0 (rawWordAt .hat j))) = true
  rw [kept1A_partition]
  exact reject1A_11_slice0
set_option maxRecDepth 100000 in
theorem reject1A_11 : rejectionCheckB 1 .hat 11 = true := by
  change (rawWordAt .hat 11).contains 0 && alignmentValidB .hat 0 && noSupportB 1 .hat 11 0 = true
  rw [reject1A_11_none]
  rfl
end SpectreClusters.StageA
