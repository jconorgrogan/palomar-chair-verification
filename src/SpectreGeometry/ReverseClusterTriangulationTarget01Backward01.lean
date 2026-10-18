module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1BackwardRoot24 : CoverTree := .leaf 62 [⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩]
theorem target1BackwardRoot24_checked : checkTree [(-1,-1,24),(2,-1,-156),(1,4,102),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot24 = true := by decide

def target1BackwardRoot25 : CoverTree := .split (2,1,-72) (.leaf 62 [⟨4,[(2,3),(4,1),(3,36)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 63 [⟨1,[(4,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨3,[(0,2),(1,1),(3,18)]⟩,⟨3,[(0,1),(1,2),(3,36)]⟩])
theorem target1BackwardRoot25_checked : checkTree [(1,-2,-132),(1,4,102),(-2,1,156),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot25 = true := by decide

def target1BackwardRoot26 : CoverTree := .split (-2,-1,72) (.leaf 63 [⟨1,[(4,1)]⟩,⟨5,[(0,2),(4,1),(3,12)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 62 [⟨9,[(1,5),(2,4),(3,90)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨6,[(0,1),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot26_checked : checkTree [(1,-2,-132),(-1,5,258),(-1,-4,-102),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot26 = true := by decide

def target1BackwardRoot27 : CoverTree := .leaf 71 [⟨1,[(1,1)]⟩,⟨3,[(0,1),(2,1),(3,18)]⟩,⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target1BackwardRoot27_checked : checkTree [(-1,1,72),(-1,-2,36),(4,-1,-234),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot27 = true := by decide

def target1BackwardRoot28 : CoverTree := .leaf 70 [⟨1,[(0,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(2,1)]⟩]
theorem target1BackwardRoot28_checked : checkTree [(-2,-1,108),(5,1,-270),(1,2,-36),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot28 = true := by decide

def target1BackwardRoot29 : CoverTree := .leaf 70 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(1,1)]⟩]
theorem target1BackwardRoot29_checked : checkTree [(1,0,-54),(1,2,-36),(-5,-1,270),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot29 = true := by decide

def target1BackwardRoot30 : CoverTree := .leaf 71 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩]
theorem target1BackwardRoot30_checked : checkTree [(1,0,-54),(-4,1,234),(-1,-2,36),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot30 = true := by decide

def target1BackwardRoot31 : CoverTree := .split (-1,-2,36) (.leaf 71 [⟨1,[(4,1)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 70 [⟨2,[(0,1),(1,1),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot31_checked : checkTree [(-1,0,54),(-3,-2,144),(6,1,-306),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot31 = true := by decide

theorem targetMeshFamily1Chunk3_covered : FamilyCover targetMeshFamily1Chunk3 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk3,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot24,target1BackwardRoot24_checked⟩
  · exact ⟨target1BackwardRoot25,target1BackwardRoot25_checked⟩
  · exact ⟨target1BackwardRoot26,target1BackwardRoot26_checked⟩
  · exact ⟨target1BackwardRoot27,target1BackwardRoot27_checked⟩
  · exact ⟨target1BackwardRoot28,target1BackwardRoot28_checked⟩
  · exact ⟨target1BackwardRoot29,target1BackwardRoot29_checked⟩
  · exact ⟨target1BackwardRoot30,target1BackwardRoot30_checked⟩
  · exact ⟨target1BackwardRoot31,target1BackwardRoot31_checked⟩

def target1BackwardRoot32 : CoverTree := .leaf 70 [⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨9,[(1,2),(2,1),(3,36)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target1BackwardRoot32_checked : checkTree [(-1,0,54),(3,-1,-162),(3,2,-144),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot32 = true := by decide

def target1BackwardRoot33 : CoverTree := .leaf 70 [⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩]
theorem target1BackwardRoot33_checked : checkTree [(0,-1,0),(3,2,-144),(-3,1,162),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot33 = true := by decide

def target1BackwardRoot34 : CoverTree := .split (1,2,-36) (.leaf 70 [⟨4,[(2,3),(4,1),(3,36)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 71 [⟨1,[(4,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨3,[(0,2),(1,1),(3,18)]⟩,⟨3,[(0,1),(1,2),(3,36)]⟩])
theorem target1BackwardRoot34_checked : checkTree [(3,1,-144),(-3,1,162),(-3,-2,144),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot34 = true := by decide

def target1BackwardRoot35 : CoverTree := .split (-1,-2,36) (.leaf 71 [⟨1,[(4,1)]⟩,⟨5,[(0,2),(4,1),(3,12)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 70 [⟨9,[(1,5),(2,4),(3,90)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨6,[(0,1),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot35_checked : checkTree [(3,1,-144),(-6,-1,306),(3,-1,-162),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot35 = true := by decide

def target1BackwardRoot36 : CoverTree := .leaf 23 [⟨1,[(1,1)]⟩,⟨3,[(0,1),(2,1),(3,18)]⟩,⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target1BackwardRoot36_checked : checkTree [(-2,-1,36),(1,-1,36),(5,4,-126),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot36 = true := by decide

def target1BackwardRoot37 : CoverTree := .leaf 22 [⟨1,[(0,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(2,1)]⟩]
theorem target1BackwardRoot37_checked : checkTree [(-1,-2,72),(4,5,-162),(-1,1,-36),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot37 = true := by decide

def target1BackwardRoot38 : CoverTree := .leaf 22 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(1,1)]⟩]
theorem target1BackwardRoot38_checked : checkTree [(1,1,-30),(-1,1,-36),(-4,-5,162),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot38 = true := by decide

def target1BackwardRoot39 : CoverTree := .leaf 23 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩]
theorem target1BackwardRoot39_checked : checkTree [(1,1,-30),(-5,-4,126),(1,-1,36),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot39 = true := by decide

theorem targetMeshFamily1Chunk4_covered : FamilyCover targetMeshFamily1Chunk4 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk4,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot32,target1BackwardRoot32_checked⟩
  · exact ⟨target1BackwardRoot33,target1BackwardRoot33_checked⟩
  · exact ⟨target1BackwardRoot34,target1BackwardRoot34_checked⟩
  · exact ⟨target1BackwardRoot35,target1BackwardRoot35_checked⟩
  · exact ⟨target1BackwardRoot36,target1BackwardRoot36_checked⟩
  · exact ⟨target1BackwardRoot37,target1BackwardRoot37_checked⟩
  · exact ⟨target1BackwardRoot38,target1BackwardRoot38_checked⟩
  · exact ⟨target1BackwardRoot39,target1BackwardRoot39_checked⟩

def target1BackwardRoot40 : CoverTree := .split (1,-1,36) (.leaf 23 [⟨1,[(4,1)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 22 [⟨2,[(0,1),(1,1),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot40_checked : checkTree [(-1,-1,30),(-1,-3,96),(5,6,-174),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot40 = true := by decide

def target1BackwardRoot41 : CoverTree := .leaf 22 [⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨9,[(1,2),(2,1),(3,36)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target1BackwardRoot41_checked : checkTree [(-1,-1,30),(4,3,-78),(1,3,-96),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot41 = true := by decide

def target1BackwardRoot42 : CoverTree := .leaf 22 [⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩]
theorem target1BackwardRoot42_checked : checkTree [(1,0,12),(1,3,-96),(-4,-3,78),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot42 = true := by decide

def target1BackwardRoot43 : CoverTree := .split (-1,1,-36) (.leaf 22 [⟨4,[(2,3),(4,1),(3,36)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 23 [⟨1,[(4,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨3,[(0,2),(1,1),(3,18)]⟩,⟨3,[(0,1),(1,2),(3,36)]⟩])
theorem target1BackwardRoot43_checked : checkTree [(2,3,-84),(-4,-3,78),(-1,-3,96),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot43 = true := by decide

def target1BackwardRoot44 : CoverTree := .split (1,-1,36) (.leaf 23 [⟨1,[(4,1)]⟩,⟨5,[(0,2),(4,1),(3,12)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 22 [⟨9,[(1,5),(2,4),(3,90)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨6,[(0,1),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot44_checked : checkTree [(2,3,-84),(-5,-6,174),(4,3,-78),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot44 = true := by decide

def target1BackwardRoot45 : CoverTree := .leaf 27 [⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨2,[(0,5),(2,3)]⟩]
theorem target1BackwardRoot45_checked : checkTree [(1,-1,36),(0,1,-6),(-3,1,-84),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot45 = true := by decide

def target1BackwardRoot46 : CoverTree := .leaf 27 [⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨2,[(0,3),(1,1)]⟩,⟨3,[(1,2),(2,1),(3,30)]⟩]
theorem target1BackwardRoot46_checked : checkTree [(1,1,24),(-3,-1,-72),(0,-1,6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot46 = true := by decide

def target1BackwardRoot47 : CoverTree := .leaf 27 [⟨3,[(1,4),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,2),(1,1),(3,6)]⟩]
theorem target1BackwardRoot47_checked : checkTree [(-1,0,-24),(0,-1,6),(3,1,72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot47 = true := by decide

theorem targetMeshFamily1Chunk5_covered : FamilyCover targetMeshFamily1Chunk5 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk5,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot40,target1BackwardRoot40_checked⟩
  · exact ⟨target1BackwardRoot41,target1BackwardRoot41_checked⟩
  · exact ⟨target1BackwardRoot42,target1BackwardRoot42_checked⟩
  · exact ⟨target1BackwardRoot43,target1BackwardRoot43_checked⟩
  · exact ⟨target1BackwardRoot44,target1BackwardRoot44_checked⟩
  · exact ⟨target1BackwardRoot45,target1BackwardRoot45_checked⟩
  · exact ⟨target1BackwardRoot46,target1BackwardRoot46_checked⟩
  · exact ⟨target1BackwardRoot47,target1BackwardRoot47_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
