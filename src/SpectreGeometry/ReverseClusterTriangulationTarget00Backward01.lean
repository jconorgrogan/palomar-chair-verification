module

public import SpectreGeometry.ReverseClusterTriangulationTarget00Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target0BackwardRoot24 : CoverTree := .leaf 62 [⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩]
theorem target0BackwardRoot24_checked : checkTree [(-1,-1,24),(2,-1,-156),(1,4,102),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot24 = true := by decide

def target0BackwardRoot25 : CoverTree := .split (2,1,-72) (.leaf 62 [⟨4,[(2,3),(4,1),(3,36)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 63 [⟨1,[(4,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨3,[(0,2),(1,1),(3,18)]⟩,⟨3,[(0,1),(1,2),(3,36)]⟩])
theorem target0BackwardRoot25_checked : checkTree [(1,-2,-132),(1,4,102),(-2,1,156),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot25 = true := by decide

def target0BackwardRoot26 : CoverTree := .split (-2,-1,72) (.leaf 63 [⟨1,[(4,1)]⟩,⟨5,[(0,2),(4,1),(3,12)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 62 [⟨9,[(1,5),(2,4),(3,90)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨6,[(0,1),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot26_checked : checkTree [(1,-2,-132),(-1,5,258),(-1,-4,-102),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot26 = true := by decide

def target0BackwardRoot27 : CoverTree := .leaf 65 [⟨1,[(1,1)]⟩,⟨3,[(0,1),(2,1),(3,18)]⟩,⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target0BackwardRoot27_checked : checkTree [(-2,-1,72),(1,-1,-72),(5,4,-126),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot27 = true := by decide

def target0BackwardRoot28 : CoverTree := .leaf 64 [⟨1,[(0,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(2,1)]⟩]
theorem target0BackwardRoot28_checked : checkTree [(-1,-2,0),(4,5,-54),(-1,1,72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot28 = true := by decide

def target0BackwardRoot29 : CoverTree := .leaf 64 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(1,1)]⟩]
theorem target0BackwardRoot29_checked : checkTree [(1,1,-18),(-1,1,72),(-4,-5,54),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot29 = true := by decide

def target0BackwardRoot30 : CoverTree := .leaf 65 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩]
theorem target0BackwardRoot30_checked : checkTree [(1,1,-18),(-5,-4,126),(1,-1,-72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot30 = true := by decide

def target0BackwardRoot31 : CoverTree := .leaf 15 [⟨1,[(1,1)]⟩,⟨3,[(0,1),(2,1),(3,18)]⟩,⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target0BackwardRoot31_checked : checkTree [(-1,1,36),(-1,-2,36),(4,-1,-126),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot31 = true := by decide

theorem targetMeshFamily0Chunk3_covered : FamilyCover targetMeshFamily0Chunk3 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk3,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot24,target0BackwardRoot24_checked⟩
  · exact ⟨target0BackwardRoot25,target0BackwardRoot25_checked⟩
  · exact ⟨target0BackwardRoot26,target0BackwardRoot26_checked⟩
  · exact ⟨target0BackwardRoot27,target0BackwardRoot27_checked⟩
  · exact ⟨target0BackwardRoot28,target0BackwardRoot28_checked⟩
  · exact ⟨target0BackwardRoot29,target0BackwardRoot29_checked⟩
  · exact ⟨target0BackwardRoot30,target0BackwardRoot30_checked⟩
  · exact ⟨target0BackwardRoot31,target0BackwardRoot31_checked⟩

def target0BackwardRoot32 : CoverTree := .leaf 14 [⟨1,[(0,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(2,1)]⟩]
theorem target0BackwardRoot32_checked : checkTree [(-2,-1,72),(5,1,-162),(1,2,-36),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot32 = true := by decide

def target0BackwardRoot33 : CoverTree := .leaf 14 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(1,1)]⟩]
theorem target0BackwardRoot33_checked : checkTree [(1,0,-30),(1,2,-36),(-5,-1,162),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot33 = true := by decide

def target0BackwardRoot34 : CoverTree := .leaf 15 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩]
theorem target0BackwardRoot34_checked : checkTree [(1,0,-30),(-4,1,126),(-1,-2,36),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot34 = true := by decide

def target0BackwardRoot35 : CoverTree := .split (-1,-2,36) (.leaf 15 [⟨1,[(4,1)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 14 [⟨2,[(0,1),(1,1),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot35_checked : checkTree [(-1,0,30),(-3,-2,96),(6,1,-174),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot35 = true := by decide

def target0BackwardRoot36 : CoverTree := .leaf 14 [⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨9,[(1,2),(2,1),(3,36)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target0BackwardRoot36_checked : checkTree [(-1,0,30),(3,-1,-78),(3,2,-96),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot36 = true := by decide

def target0BackwardRoot37 : CoverTree := .leaf 14 [⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩]
theorem target0BackwardRoot37_checked : checkTree [(0,-1,12),(3,2,-96),(-3,1,78),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot37 = true := by decide

def target0BackwardRoot38 : CoverTree := .split (1,2,-36) (.leaf 14 [⟨4,[(2,3),(4,1),(3,36)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 15 [⟨1,[(4,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨3,[(0,2),(1,1),(3,18)]⟩,⟨3,[(0,1),(1,2),(3,36)]⟩])
theorem target0BackwardRoot38_checked : checkTree [(3,1,-84),(-3,1,78),(-3,-2,96),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot38 = true := by decide

def target0BackwardRoot39 : CoverTree := .split (-1,-2,36) (.leaf 15 [⟨1,[(4,1)]⟩,⟨5,[(0,2),(4,1),(3,12)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 14 [⟨9,[(1,5),(2,4),(3,90)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨6,[(0,1),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot39_checked : checkTree [(3,1,-84),(-6,-1,174),(3,-1,-78),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot39 = true := by decide

theorem targetMeshFamily0Chunk4_covered : FamilyCover targetMeshFamily0Chunk4 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk4,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot32,target0BackwardRoot32_checked⟩
  · exact ⟨target0BackwardRoot33,target0BackwardRoot33_checked⟩
  · exact ⟨target0BackwardRoot34,target0BackwardRoot34_checked⟩
  · exact ⟨target0BackwardRoot35,target0BackwardRoot35_checked⟩
  · exact ⟨target0BackwardRoot36,target0BackwardRoot36_checked⟩
  · exact ⟨target0BackwardRoot37,target0BackwardRoot37_checked⟩
  · exact ⟨target0BackwardRoot38,target0BackwardRoot38_checked⟩
  · exact ⟨target0BackwardRoot39,target0BackwardRoot39_checked⟩

def target0BackwardRoot40 : CoverTree := .leaf 23 [⟨1,[(1,1)]⟩,⟨3,[(0,1),(2,1),(3,18)]⟩,⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target0BackwardRoot40_checked : checkTree [(-2,-1,36),(1,-1,36),(5,4,-126),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot40 = true := by decide

def target0BackwardRoot41 : CoverTree := .leaf 22 [⟨1,[(0,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(2,1)]⟩]
theorem target0BackwardRoot41_checked : checkTree [(-1,-2,72),(4,5,-162),(-1,1,-36),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot41 = true := by decide

def target0BackwardRoot42 : CoverTree := .leaf 22 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(1,1)]⟩]
theorem target0BackwardRoot42_checked : checkTree [(1,1,-30),(-1,1,-36),(-4,-5,162),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot42 = true := by decide

def target0BackwardRoot43 : CoverTree := .leaf 23 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩]
theorem target0BackwardRoot43_checked : checkTree [(1,1,-30),(-5,-4,126),(1,-1,36),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot43 = true := by decide

def target0BackwardRoot44 : CoverTree := .split (1,-1,36) (.leaf 23 [⟨1,[(4,1)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 22 [⟨2,[(0,1),(1,1),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot44_checked : checkTree [(-1,-1,30),(-1,-3,96),(5,6,-174),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot44 = true := by decide

def target0BackwardRoot45 : CoverTree := .leaf 22 [⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨9,[(1,2),(2,1),(3,36)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target0BackwardRoot45_checked : checkTree [(-1,-1,30),(4,3,-78),(1,3,-96),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot45 = true := by decide

def target0BackwardRoot46 : CoverTree := .leaf 22 [⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩]
theorem target0BackwardRoot46_checked : checkTree [(1,0,12),(1,3,-96),(-4,-3,78),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot46 = true := by decide

def target0BackwardRoot47 : CoverTree := .split (-1,1,-36) (.leaf 22 [⟨4,[(2,3),(4,1),(3,36)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 23 [⟨1,[(4,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨3,[(0,2),(1,1),(3,18)]⟩,⟨3,[(0,1),(1,2),(3,36)]⟩])
theorem target0BackwardRoot47_checked : checkTree [(2,3,-84),(-4,-3,78),(-1,-3,96),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot47 = true := by decide

theorem targetMeshFamily0Chunk5_covered : FamilyCover targetMeshFamily0Chunk5 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk5,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot40,target0BackwardRoot40_checked⟩
  · exact ⟨target0BackwardRoot41,target0BackwardRoot41_checked⟩
  · exact ⟨target0BackwardRoot42,target0BackwardRoot42_checked⟩
  · exact ⟨target0BackwardRoot43,target0BackwardRoot43_checked⟩
  · exact ⟨target0BackwardRoot44,target0BackwardRoot44_checked⟩
  · exact ⟨target0BackwardRoot45,target0BackwardRoot45_checked⟩
  · exact ⟨target0BackwardRoot46,target0BackwardRoot46_checked⟩
  · exact ⟨target0BackwardRoot47,target0BackwardRoot47_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
