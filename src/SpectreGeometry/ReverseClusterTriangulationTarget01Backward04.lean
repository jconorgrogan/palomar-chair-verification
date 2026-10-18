module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1BackwardRoot96 : CoverTree := .leaf 32 [⟨2,[(0,5),(2,1),(3,12)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(1,1)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩]
theorem target1BackwardRoot96_checked : checkTree [(0,-1,24),(1,1,0),(-2,1,-60),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot96 = true := by decide

def target1BackwardRoot97 : CoverTree := .leaf 26 [⟨3,[(1,2),(2,1),(3,12)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨2,[(0,5),(1,1),(3,12)]⟩]
theorem target1BackwardRoot97_checked : checkTree [(1,0,24),(-1,2,-60),(-1,-1,0),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot97 = true := by decide

def target1BackwardRoot98 : CoverTree := .leaf 26 [⟨1,[(0,1),(1,1)]⟩,⟨1,[(1,1),(2,1)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩,⟨1,[(0,4),(1,1)]⟩]
theorem target1BackwardRoot98_checked : checkTree [(1,0,24),(-2,1,-60),(1,-2,60),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot98 = true := by decide

def target1BackwardRoot99 : CoverTree := .leaf 26 [⟨1,[(0,1)]⟩,⟨1,[(1,1)]⟩,⟨3,[(1,2),(2,1),(3,12)]⟩,⟨1,[(0,4),(2,3)]⟩]
theorem target1BackwardRoot99_checked : checkTree [(-1,1,-36),(-1,-1,0),(2,-1,60),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot99 = true := by decide

def target1BackwardRoot100 : CoverTree := .leaf 32 [⟨1,[(0,4),(1,3)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,1)]⟩]
theorem target1BackwardRoot100_checked : checkTree [(-1,1,-36),(1,-2,60),(1,1,0),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot100 = true := by decide

def target1BackwardRoot101 : CoverTree := .split (1,1,0) (.leaf 33 [⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(1,1),(2,1)]⟩,⟨1,[(0,7),(2,3)]⟩]) (.leaf 29 [⟨3,[(1,8),(2,7),(3,12)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩])
theorem target1BackwardRoot101_checked : checkTree [(1,-1,36),(3,-1,72),(-3,2,-84),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot101 = true := by decide

def target1BackwardRoot102 : CoverTree := .leaf 29 [⟨1,[(0,1),(1,3)]⟩,⟨2,[(0,1),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,1)]⟩]
theorem target1BackwardRoot102_checked : checkTree [(1,-1,36),(0,1,-12),(-3,1,-72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot102 = true := by decide

def target1BackwardRoot103 : CoverTree := .split (2,1,36) (.split (-1,-2,0) (.leaf 28 [⟨1,[(4,1)]⟩,⟨2,[(0,3),(1,1),(3,12)]⟩,⟨3,[(1,1),(2,2),(3,24)]⟩,⟨1,[(5,1)]⟩]) (.leaf 29 [⟨1,[(5,1)]⟩,⟨3,[(1,1),(2,2),(3,24)]⟩,⟨3,[(1,1),(2,5),(3,24)]⟩,⟨1,[(0,1),(2,1)]⟩])) (.leaf 27 [⟨1,[(0,1),(2,1)]⟩,⟨2,[(0,5),(1,1),(3,12)]⟩,⟨2,[(0,3),(1,1),(3,12)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot103_checked : checkTree [(1,0,24),(-3,2,-84),(0,-1,12),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot103 = true := by decide

theorem targetMeshFamily1Chunk12_covered : FamilyCover targetMeshFamily1Chunk12 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk12,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot96,target1BackwardRoot96_checked⟩
  · exact ⟨target1BackwardRoot97,target1BackwardRoot97_checked⟩
  · exact ⟨target1BackwardRoot98,target1BackwardRoot98_checked⟩
  · exact ⟨target1BackwardRoot99,target1BackwardRoot99_checked⟩
  · exact ⟨target1BackwardRoot100,target1BackwardRoot100_checked⟩
  · exact ⟨target1BackwardRoot101,target1BackwardRoot101_checked⟩
  · exact ⟨target1BackwardRoot102,target1BackwardRoot102_checked⟩
  · exact ⟨target1BackwardRoot103,target1BackwardRoot103_checked⟩

def target1BackwardRoot104 : CoverTree := .split (-2,-1,-36) (.leaf 27 [⟨1,[(0,3),(4,1)]⟩,⟨1,[(0,4),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(4,1)]⟩]) (.split (-1,-2,0) (.leaf 28 [⟨1,[(4,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨3,[(1,2),(2,1),(3,24)]⟩,⟨1,[(5,1)]⟩]) (.leaf 29 [⟨1,[(5,1)]⟩,⟨3,[(1,2),(2,1),(3,24)]⟩,⟨3,[(1,5),(2,4),(3,24)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩]))
theorem target1BackwardRoot104_checked : checkTree [(1,0,24),(-3,1,-72),(3,-2,84),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot104 = true := by decide

def target1BackwardRoot105 : CoverTree := .split (-1,-2,0) (.split (2,1,36) (.leaf 28 [⟨1,[(5,1)]⟩,⟨1,[(0,3),(2,2)]⟩,⟨2,[(0,1),(1,1),(3,12)]⟩,⟨1,[(4,1)]⟩]) (.leaf 27 [⟨3,[(1,2),(2,1),(3,12)]⟩,⟨1,[(0,4),(2,3)]⟩,⟨1,[(0,3),(2,2)]⟩,⟨1,[(5,1)]⟩])) (.leaf 29 [⟨1,[(4,1)]⟩,⟨2,[(0,1),(1,1),(3,12)]⟩,⟨2,[(0,1),(1,3),(3,12)]⟩,⟨1,[(1,3),(4,1)]⟩])
theorem target1BackwardRoot105_checked : checkTree [(-2,1,-48),(0,-1,12),(3,-1,72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot105 = true := by decide

def target1BackwardRoot106 : CoverTree := .split (-1,-1,0) (.leaf 29 [⟨3,[(1,1),(2,8),(3,12)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1),(1,1)]⟩]) (.leaf 33 [⟨1,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,7),(1,4)]⟩])
theorem target1BackwardRoot106_checked : checkTree [(-2,1,-48),(3,-2,84),(0,1,-12),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot106 = true := by decide

def target1BackwardRoot107 : CoverTree := .split (-1,-1,0) (.split (1,2,0) (.leaf 29 [⟨1,[(5,1)]⟩,⟨1,[(0,4),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,5),(2,1)]⟩]) (.leaf 28 [⟨3,[(1,17),(2,5),(3,6)]⟩,⟨1,[(1,3),(2,1),(3,6)]⟩,⟨1,[(0,4),(2,1)]⟩,⟨1,[(5,1)]⟩])) (.leaf 33 [⟨1,[(0,5),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨13,[(2,1),(4,9),(3,48)]⟩,⟨1,[(0,17),(2,4)]⟩])
theorem target1BackwardRoot107_checked : checkTree [(2,-1,48),(3,-1,66),(-9,4,-204),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot107 = true := by decide

def target1BackwardRoot108 : CoverTree := .split (2,1,36) (.split (-1,-2,0) (.leaf 28 [⟨1,[(4,1)]⟩,⟨1,[(0,3),(1,2)]⟩,⟨1,[(0,1),(2,1),(3,6)]⟩,⟨1,[(5,1)]⟩]) (.leaf 29 [⟨1,[(5,1)]⟩,⟨1,[(0,1),(2,1),(3,6)]⟩,⟨1,[(0,4),(2,3),(3,6)]⟩,⟨1,[(0,2),(2,1),(3,6)]⟩])) (.leaf 27 [⟨1,[(0,2),(2,1),(3,6)]⟩,⟨1,[(0,5),(1,3)]⟩,⟨1,[(0,3),(1,2)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot108_checked : checkTree [(2,-1,48),(-3,2,-72),(-3,1,-66),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot108 = true := by decide

def target1BackwardRoot109 : CoverTree := .split (0,1,0) (.split (-2,-1,-36) (.leaf 27 [⟨1,[(0,3),(5,1)]⟩,⟨1,[(0,1),(4,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 28 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨3,[(1,2),(2,1),(3,24)]⟩,⟨3,[(1,8),(2,7),(3,24)]⟩])) (.leaf 35 [⟨3,[(1,2),(4,5),(3,24)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,7),(1,2)]⟩])
theorem target1BackwardRoot109_checked : checkTree [(1,0,24),(-3,1,-66),(3,-2,72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot109 = true := by decide

def target1BackwardRoot110 : CoverTree := .split (-2,-1,-36) (.split (0,1,0) (.leaf 27 [⟨4,[(0,1),(1,3),(3,36)]⟩,⟨3,[(1,1),(5,5)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 35 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,7),(2,12)]⟩])) (.leaf 28 [⟨1,[(4,1)]⟩,⟨9,[(0,2),(4,5),(3,36)]⟩,⟨2,[(0,1),(1,1),(3,12)]⟩,⟨1,[(0,2),(1,3)]⟩])
theorem target1BackwardRoot110_checked : checkTree [(-5,2,-108),(3,-2,72),(3,-1,66),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot110 = true := by decide

def target1BackwardRoot111 : CoverTree := .split (-1,-1,0) (.split (1,2,0) (.leaf 29 [⟨1,[(5,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(4,1)]⟩,⟨2,[(0,5),(1,3)]⟩]) (.leaf 28 [⟨6,[(1,7),(2,17),(3,12)]⟩,⟨2,[(1,1),(2,3),(3,12)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(5,1)]⟩])) (.leaf 33 [⟨2,[(0,5),(1,3)]⟩,⟨1,[(4,1)]⟩,⟨5,[(2,1),(4,3),(3,12)]⟩,⟨2,[(0,17),(1,9)]⟩])
theorem target1BackwardRoot111_checked : checkTree [(-5,2,-108),(9,-4,204),(-3,2,-72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot111 = true := by decide

theorem targetMeshFamily1Chunk13_covered : FamilyCover targetMeshFamily1Chunk13 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk13,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot104,target1BackwardRoot104_checked⟩
  · exact ⟨target1BackwardRoot105,target1BackwardRoot105_checked⟩
  · exact ⟨target1BackwardRoot106,target1BackwardRoot106_checked⟩
  · exact ⟨target1BackwardRoot107,target1BackwardRoot107_checked⟩
  · exact ⟨target1BackwardRoot108,target1BackwardRoot108_checked⟩
  · exact ⟨target1BackwardRoot109,target1BackwardRoot109_checked⟩
  · exact ⟨target1BackwardRoot110,target1BackwardRoot110_checked⟩
  · exact ⟨target1BackwardRoot111,target1BackwardRoot111_checked⟩

def target1BackwardRoot112 : CoverTree := .split (1,2,-36) (.leaf 25 [⟨1,[(4,1)]⟩,⟨3,[(0,4),(2,1),(3,18)]⟩,⟨3,[(0,11),(2,2)]⟩,⟨1,[(0,1)]⟩]) (.split (-2,-1,0) (.leaf 33 [⟨1,[(0,1)]⟩,⟨9,[(1,11),(2,5),(3,18)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩,⟨1,[(5,1)]⟩]) (.leaf 24 [⟨1,[(5,1)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩,⟨3,[(0,4),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩]))
theorem target1BackwardRoot112_checked : checkTree [(1,-1,36),(4,-1,72),(-7,4,-162),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot112 = true := by decide

def target1BackwardRoot113 : CoverTree := .split (1,1,0) (.leaf 33 [⟨1,[(0,1),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨5,[(2,1),(4,4),(3,12)]⟩,⟨1,[(0,2),(2,3)]⟩]) (.leaf 29 [⟨1,[(0,3),(1,2)]⟩,⟨3,[(0,1),(2,2)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1),(2,1)]⟩])
theorem target1BackwardRoot113_checked : checkTree [(5,-2,108),(-7,4,-162),(-4,1,-72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot113 = true := by decide

def target1BackwardRoot114 : CoverTree := .split (-1,-2,0) (.split (2,1,36) (.leaf 28 [⟨1,[(5,1)]⟩,⟨21,[(1,2),(5,11),(3,72)]⟩,⟨9,[(1,4),(2,5),(3,18)]⟩,⟨1,[(4,1)]⟩]) (.split (0,1,0) (.leaf 27 [⟨3,[(0,1),(5,1),(3,36)]⟩,⟨5,[(0,1),(6,7),(3,12)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 35 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨1,[(0,9),(1,4)]⟩]))) (.split (-1,-1,0) (.leaf 29 [⟨1,[(4,1)]⟩,⟨9,[(1,4),(2,5),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩]) (.leaf 33 [⟨3,[(1,1),(2,2),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨16,[(1,1),(5,11),(3,42)]⟩,⟨3,[(1,5),(2,7),(3,36)]⟩]))
theorem target1BackwardRoot114_checked : checkTree [(5,-2,108),(-11,5,-234),(7,-4,162),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot114 = true := by decide

def target1BackwardRoot115 : CoverTree := .split (-1,-2,0) (.split (2,1,36) (.leaf 28 [⟨1,[(5,1)]⟩,⟨2,[(0,1),(5,1),(3,6)]⟩,⟨5,[(0,2),(4,1),(3,24)]⟩,⟨1,[(4,1)]⟩]) (.split (0,1,0) (.leaf 27 [⟨3,[(1,2),(2,1),(3,18)]⟩,⟨11,[(2,1),(6,16),(3,30)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 35 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,27),(2,5)]⟩]))) (.split (-1,-1,0) (.leaf 29 [⟨1,[(4,1)]⟩,⟨3,[(0,1),(5,1),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩]) (.leaf 33 [⟨3,[(1,2),(2,1),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨3,[(0,1),(5,2),(3,6)]⟩,⟨3,[(1,7),(2,2),(3,36)]⟩]))
theorem target1BackwardRoot115_checked : checkTree [(-2,1,-42),(-4,1,-72),(11,-5,234),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot115 = true := by decide

def target1BackwardRoot116 : CoverTree := .split (-2,-1,0) (.split (1,1,0) (.leaf 33 [⟨1,[(0,3),(1,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 29 [⟨2,[(0,9),(2,5),(3,18)]⟩,⟨3,[(0,1),(5,1),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,3),(1,1)]⟩])) (.split (1,2,-36) (.leaf 25 [⟨1,[(5,1)]⟩,⟨1,[(0,4),(1,1),(3,6)]⟩,⟨1,[(0,11),(1,3)]⟩,⟨1,[(0,3),(1,1)]⟩]) (.leaf 24 [⟨1,[(4,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,4),(1,1),(3,6)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot116_checked : checkTree [(-2,1,-42),(7,-4,162),(4,-1,72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot116 = true := by decide

def target1BackwardRoot117 : CoverTree := .split (1,1,0) (.split (-2,-1,0) (.leaf 33 [⟨1,[(0,7),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨19,[(2,1),(4,13),(3,30)]⟩,⟨1,[(5,1)]⟩]) (.split (1,2,-36) (.leaf 25 [⟨1,[(6,1)]⟩,⟨1,[(0,6),(2,1),(3,6)]⟩,⟨1,[(0,19),(2,3)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 24 [⟨1,[(5,1)]⟩,⟨19,[(2,1),(4,13),(3,30)]⟩,⟨1,[(0,6),(2,1),(3,6)]⟩,⟨1,[(6,1)]⟩]))) (.split (1,2,0) (.leaf 29 [⟨1,[(5,1)]⟩,⟨19,[(2,1),(4,6),(3,30)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 28 [⟨9,[(1,25),(2,14),(3,36)]⟩,⟨9,[(1,13),(2,8),(3,36)]⟩,⟨16,[(2,1),(5,3),(3,66)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot117_checked : checkTree [(2,-1,42),(8,-3,156),(-13,6,-258),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot117 = true := by decide

def target1BackwardRoot118 : CoverTree := .split (2,1,36) (.split (-1,-2,0) (.leaf 28 [⟨1,[(4,1)]⟩,⟨7,[(2,1),(4,4),(3,12)]⟩,⟨2,[(0,3),(2,1),(3,6)]⟩,⟨1,[(5,1)]⟩]) (.leaf 29 [⟨1,[(5,1)]⟩,⟨2,[(0,3),(2,1),(3,6)]⟩,⟨2,[(0,11),(2,3),(3,6)]⟩,⟨2,[(0,5),(2,1),(3,18)]⟩])) (.split (0,-1,0) (.leaf 35 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,13),(1,5)]⟩]) (.leaf 27 [⟨2,[(0,5),(2,1),(3,18)]⟩,⟨2,[(0,1),(5,3),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]))
theorem target1BackwardRoot118_checked : checkTree [(2,-1,42),(-5,3,-102),(-8,3,-156),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot118 = true := by decide

def target1BackwardRoot119 : CoverTree := .split (1,2,36) (.split (0,-1,0) (.leaf 35 [⟨4,[(1,1),(5,7),(3,12)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩]) (.split (-2,-1,-36) (.leaf 27 [⟨1,[(0,3),(6,1)]⟩,⟨1,[(0,1),(5,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 28 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨3,[(1,1),(2,1),(3,18)]⟩,⟨9,[(1,13),(2,19),(3,90)]⟩]))) (.leaf 36 [⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨3,[(0,11),(1,1)]⟩,⟨3,[(0,5),(1,1),(3,36)]⟩])
theorem target1BackwardRoot119_checked : checkTree [(1,0,24),(-8,3,-156),(5,-3,102),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot119 = true := by decide

theorem targetMeshFamily1Chunk14_covered : FamilyCover targetMeshFamily1Chunk14 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk14,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot112,target1BackwardRoot112_checked⟩
  · exact ⟨target1BackwardRoot113,target1BackwardRoot113_checked⟩
  · exact ⟨target1BackwardRoot114,target1BackwardRoot114_checked⟩
  · exact ⟨target1BackwardRoot115,target1BackwardRoot115_checked⟩
  · exact ⟨target1BackwardRoot116,target1BackwardRoot116_checked⟩
  · exact ⟨target1BackwardRoot117,target1BackwardRoot117_checked⟩
  · exact ⟨target1BackwardRoot118,target1BackwardRoot118_checked⟩
  · exact ⟨target1BackwardRoot119,target1BackwardRoot119_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
