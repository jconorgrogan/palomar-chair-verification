module

public import SpectreClusters.StageARejectCore

@[expose] public section

namespace SpectreClusters.StageA
set_option maxRecDepth 100000 in
theorem reject0A_172_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .hat (rawWordAt .hat 172) 9 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_172_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .hat (rawWordAt .hat 172) 9 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_172_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .hat (rawWordAt .hat 172) 9 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_172_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .hat (rawWordAt .hat 172) 9 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_172_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .hat (rawWordAt .hat 172) 9 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_172_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .hat (rawWordAt .hat 172) 9 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_172_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .hat (rawWordAt .hat 172) 9 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_172_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .hat (rawWordAt .hat 172) 9 (rawWordAt .hat j))) = true := by rfl
theorem reject0A_172_none : noSupportB 0 .hat 172 9 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 172) 9 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0A_172_slice0, reject0A_172_slice1, reject0A_172_slice2, reject0A_172_slice3, reject0A_172_slice4, reject0A_172_slice5, reject0A_172_slice6, reject0A_172_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_172 : rejectionCheckB 0 .hat 172 = true := by
  change (rawWordAt .hat 172).contains 9 && alignmentValidB .hat 9 && noSupportB 0 .hat 172 9 = true
  rw [reject0A_172_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_173_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .hat (rawWordAt .hat 173) 21 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_173_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .hat (rawWordAt .hat 173) 21 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_173_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .hat (rawWordAt .hat 173) 21 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_173_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .hat (rawWordAt .hat 173) 21 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_173_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .hat (rawWordAt .hat 173) 21 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_173_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .hat (rawWordAt .hat 173) 21 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_173_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .hat (rawWordAt .hat 173) 21 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_173_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .hat (rawWordAt .hat 173) 21 (rawWordAt .hat j))) = true := by rfl
theorem reject0A_173_none : noSupportB 0 .hat 173 21 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 173) 21 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0A_173_slice0, reject0A_173_slice1, reject0A_173_slice2, reject0A_173_slice3, reject0A_173_slice4, reject0A_173_slice5, reject0A_173_slice6, reject0A_173_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_173 : rejectionCheckB 0 .hat 173 = true := by
  change (rawWordAt .hat 173).contains 21 && alignmentValidB .hat 21 && noSupportB 0 .hat 173 21 = true
  rw [reject0A_173_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_174_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .hat (rawWordAt .hat 174) 27 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_174_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .hat (rawWordAt .hat 174) 27 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_174_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .hat (rawWordAt .hat 174) 27 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_174_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .hat (rawWordAt .hat 174) 27 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_174_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .hat (rawWordAt .hat 174) 27 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_174_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .hat (rawWordAt .hat 174) 27 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_174_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .hat (rawWordAt .hat 174) 27 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_174_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .hat (rawWordAt .hat 174) 27 (rawWordAt .hat j))) = true := by rfl
theorem reject0A_174_none : noSupportB 0 .hat 174 27 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 174) 27 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0A_174_slice0, reject0A_174_slice1, reject0A_174_slice2, reject0A_174_slice3, reject0A_174_slice4, reject0A_174_slice5, reject0A_174_slice6, reject0A_174_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_174 : rejectionCheckB 0 .hat 174 = true := by
  change (rawWordAt .hat 174).contains 27 && alignmentValidB .hat 27 && noSupportB 0 .hat 174 27 = true
  rw [reject0A_174_none]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_175_slice0 : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (fun j => !(supportB .hat (rawWordAt .hat 175) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_175_slice1 : [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun j => !(supportB .hat (rawWordAt .hat 175) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_175_slice2 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun j => !(supportB .hat (rawWordAt .hat 175) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_175_slice3 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun j => !(supportB .hat (rawWordAt .hat 175) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_175_slice4 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun j => !(supportB .hat (rawWordAt .hat 175) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_175_slice5 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun j => !(supportB .hat (rawWordAt .hat 175) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_175_slice6 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun j => !(supportB .hat (rawWordAt .hat 175) 3 (rawWordAt .hat j))) = true := by rfl
set_option maxRecDepth 100000 in
theorem reject0A_175_slice7 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250].all (fun j => !(supportB .hat (rawWordAt .hat 175) 3 (rawWordAt .hat j))) = true := by rfl
theorem reject0A_175_none : noSupportB 0 .hat 175 3 = true := by
  change (keptIds 0 .hat).all (fun j => !(supportB .hat (rawWordAt .hat 175) 3 (rawWordAt .hat j))) = true
  rw [kept0A_partition]
  simp only [List.all_append]
  rw [reject0A_175_slice0, reject0A_175_slice1, reject0A_175_slice2, reject0A_175_slice3, reject0A_175_slice4, reject0A_175_slice5, reject0A_175_slice6, reject0A_175_slice7]
  rfl
set_option maxRecDepth 100000 in
theorem reject0A_175 : rejectionCheckB 0 .hat 175 = true := by
  change (rawWordAt .hat 175).contains 3 && alignmentValidB .hat 3 && noSupportB 0 .hat 175 3 = true
  rw [reject0A_175_none]
  rfl
end SpectreClusters.StageA
