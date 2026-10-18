module

public import SpectreClusters.StageARejectCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem reject0A_44_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .hat (rawWordAt .hat 44) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_44_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .hat (rawWordAt .hat 44) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_44_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .hat (rawWordAt .hat 44) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_44_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .hat (rawWordAt .hat 44) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_44_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .hat (rawWordAt .hat 44) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_44_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .hat (rawWordAt .hat 44) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_44_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .hat (rawWordAt .hat 44) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_44_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .hat (rawWordAt .hat 44) 6 (rawWordAt .hat j))) = true := by rfl
theorem reject0A_44_none : noSupportB 0 .hat 44 6 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 44) 6 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0A_44_slice0, reject0A_44_slice1, reject0A_44_slice2, reject0A_44_slice3, reject0A_44_slice4, reject0A_44_slice5, reject0A_44_slice6, reject0A_44_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_44 : rejectionCheckB 0 .hat 44 = true := by
  change (rawWordAt .hat 44).contains 6 && alignmentValidB .hat 6 && noSupportB 0 .hat 44 6 = true
  rw [reject0A_44_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_45_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .hat (rawWordAt .hat 45) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_45_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .hat (rawWordAt .hat 45) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_45_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .hat (rawWordAt .hat 45) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_45_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .hat (rawWordAt .hat 45) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_45_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .hat (rawWordAt .hat 45) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_45_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .hat (rawWordAt .hat 45) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_45_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .hat (rawWordAt .hat 45) 6 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_45_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .hat (rawWordAt .hat 45) 6 (rawWordAt .hat j))) = true := by rfl
theorem reject0A_45_none : noSupportB 0 .hat 45 6 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 45) 6 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0A_45_slice0, reject0A_45_slice1, reject0A_45_slice2, reject0A_45_slice3, reject0A_45_slice4, reject0A_45_slice5, reject0A_45_slice6, reject0A_45_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_45 : rejectionCheckB 0 .hat 45 = true := by
  change (rawWordAt .hat 45).contains 6 && alignmentValidB .hat 6 && noSupportB 0 .hat 45 6 = true
  rw [reject0A_45_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_46_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .hat (rawWordAt .hat 46) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_46_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .hat (rawWordAt .hat 46) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_46_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .hat (rawWordAt .hat 46) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_46_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .hat (rawWordAt .hat 46) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_46_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .hat (rawWordAt .hat 46) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_46_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .hat (rawWordAt .hat 46) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_46_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .hat (rawWordAt .hat 46) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_46_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .hat (rawWordAt .hat 46) 10 (rawWordAt .hat j))) = true := by rfl
theorem reject0A_46_none : noSupportB 0 .hat 46 10 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 46) 10 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0A_46_slice0, reject0A_46_slice1, reject0A_46_slice2, reject0A_46_slice3, reject0A_46_slice4, reject0A_46_slice5, reject0A_46_slice6, reject0A_46_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_46 : rejectionCheckB 0 .hat 46 = true := by
  change (rawWordAt .hat 46).contains 10 && alignmentValidB .hat 10 && noSupportB 0 .hat 46 10 = true
  rw [reject0A_46_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_47_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .hat (rawWordAt .hat 47) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_47_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .hat (rawWordAt .hat 47) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_47_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .hat (rawWordAt .hat 47) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_47_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .hat (rawWordAt .hat 47) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_47_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .hat (rawWordAt .hat 47) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_47_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .hat (rawWordAt .hat 47) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_47_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .hat (rawWordAt .hat 47) 10 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_47_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .hat (rawWordAt .hat 47) 10 (rawWordAt .hat j))) = true := by rfl
theorem reject0A_47_none : noSupportB 0 .hat 47 10 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 47) 10 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0A_47_slice0, reject0A_47_slice1, reject0A_47_slice2, reject0A_47_slice3, reject0A_47_slice4, reject0A_47_slice5, reject0A_47_slice6, reject0A_47_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_47 : rejectionCheckB 0 .hat 47 = true := by
  change (rawWordAt .hat 47).contains 10 && alignmentValidB .hat 10 && noSupportB 0 .hat 47 10 = true
  rw [reject0A_47_none]
  rfl
end SpectreClusters.StageA
