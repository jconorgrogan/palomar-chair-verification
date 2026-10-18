module

public import SpectreClusters.StageARejectCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem reject0B_25_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .turtle (rawWordAt .turtle 25) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_25_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .turtle (rawWordAt .turtle 25) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_25_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .turtle (rawWordAt .turtle 25) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_25_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .turtle (rawWordAt .turtle 25) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_25_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .turtle (rawWordAt .turtle 25) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_25_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .turtle (rawWordAt .turtle 25) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_25_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .turtle (rawWordAt .turtle 25) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_25_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .turtle (rawWordAt .turtle 25) 3 (rawWordAt .hat j))) = true := by rfl
theorem reject0B_25_none : noSupportB 0 .turtle 25 3 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .turtle (rawWordAt .turtle 25) 3 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0B_25_slice0, reject0B_25_slice1, reject0B_25_slice2, reject0B_25_slice3, reject0B_25_slice4, reject0B_25_slice5, reject0B_25_slice6, reject0B_25_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0B_25 : rejectionCheckB 0 .turtle 25 = true := by
  change (rawWordAt .turtle 25).contains 3 && alignmentValidB .turtle 3 && noSupportB 0 .turtle 25 3 = true
  rw [reject0B_25_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject0B_26_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .turtle (rawWordAt .turtle 26) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_26_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .turtle (rawWordAt .turtle 26) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_26_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .turtle (rawWordAt .turtle 26) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_26_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .turtle (rawWordAt .turtle 26) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_26_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .turtle (rawWordAt .turtle 26) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_26_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .turtle (rawWordAt .turtle 26) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_26_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .turtle (rawWordAt .turtle 26) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_26_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .turtle (rawWordAt .turtle 26) 3 (rawWordAt .hat j))) = true := by rfl
theorem reject0B_26_none : noSupportB 0 .turtle 26 3 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .turtle (rawWordAt .turtle 26) 3 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0B_26_slice0, reject0B_26_slice1, reject0B_26_slice2, reject0B_26_slice3, reject0B_26_slice4, reject0B_26_slice5, reject0B_26_slice6, reject0B_26_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0B_26 : rejectionCheckB 0 .turtle 26 = true := by
  change (rawWordAt .turtle 26).contains 3 && alignmentValidB .turtle 3 && noSupportB 0 .turtle 26 3 = true
  rw [reject0B_26_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject0B_27_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .turtle (rawWordAt .turtle 27) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_27_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .turtle (rawWordAt .turtle 27) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_27_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .turtle (rawWordAt .turtle 27) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_27_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .turtle (rawWordAt .turtle 27) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_27_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .turtle (rawWordAt .turtle 27) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_27_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .turtle (rawWordAt .turtle 27) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_27_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .turtle (rawWordAt .turtle 27) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_27_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .turtle (rawWordAt .turtle 27) 3 (rawWordAt .hat j))) = true := by rfl
theorem reject0B_27_none : noSupportB 0 .turtle 27 3 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .turtle (rawWordAt .turtle 27) 3 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0B_27_slice0, reject0B_27_slice1, reject0B_27_slice2, reject0B_27_slice3, reject0B_27_slice4, reject0B_27_slice5, reject0B_27_slice6, reject0B_27_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0B_27 : rejectionCheckB 0 .turtle 27 = true := by
  change (rawWordAt .turtle 27).contains 3 && alignmentValidB .turtle 3 && noSupportB 0 .turtle 27 3 = true
  rw [reject0B_27_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject0B_28_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .turtle (rawWordAt .turtle 28) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_28_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .turtle (rawWordAt .turtle 28) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_28_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .turtle (rawWordAt .turtle 28) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_28_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .turtle (rawWordAt .turtle 28) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_28_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .turtle (rawWordAt .turtle 28) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_28_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .turtle (rawWordAt .turtle 28) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_28_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .turtle (rawWordAt .turtle 28) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0B_28_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .turtle (rawWordAt .turtle 28) 3 (rawWordAt .hat j))) = true := by rfl
theorem reject0B_28_none : noSupportB 0 .turtle 28 3 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .turtle (rawWordAt .turtle 28) 3 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0B_28_slice0, reject0B_28_slice1, reject0B_28_slice2, reject0B_28_slice3, reject0B_28_slice4, reject0B_28_slice5, reject0B_28_slice6, reject0B_28_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0B_28 : rejectionCheckB 0 .turtle 28 = true := by
  change (rawWordAt .turtle 28).contains 3 && alignmentValidB .turtle 3 && noSupportB 0 .turtle 28 3 = true
  rw [reject0B_28_none]
  rfl
end SpectreClusters.StageA
