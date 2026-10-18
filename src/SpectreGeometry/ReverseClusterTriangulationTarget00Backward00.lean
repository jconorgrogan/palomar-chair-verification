module

public import SpectreGeometry.ReverseClusterTriangulationTarget00Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target0BackwardRoot0 : CoverTree := .leaf 39 [⟨1,[(1,1)]⟩,⟨3,[(0,1),(2,1),(3,18)]⟩,⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target0BackwardRoot0_checked : checkTree [(1,-1,0),(1,2,72),(-4,1,-54),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot0 = true := by decide

def target0BackwardRoot1 : CoverTree := .leaf 38 [⟨1,[(0,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(2,1)]⟩]
theorem target0BackwardRoot1_checked : checkTree [(2,1,72),(-5,-1,-126),(-1,-2,-72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot1 = true := by decide

def target0BackwardRoot2 : CoverTree := .leaf 38 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(1,1)]⟩]
theorem target0BackwardRoot2_checked : checkTree [(-1,0,-18),(-1,-2,-72),(5,1,126),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot2 = true := by decide

def target0BackwardRoot3 : CoverTree := .leaf 39 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩]
theorem target0BackwardRoot3_checked : checkTree [(-1,0,-18),(4,-1,54),(1,2,72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot3 = true := by decide

def target0BackwardRoot4 : CoverTree := .split (1,2,72) (.leaf 39 [⟨1,[(4,1)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 38 [⟨2,[(0,1),(1,1),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot4_checked : checkTree [(1,0,18),(3,2,108),(-6,-1,-126),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot4 = true := by decide

def target0BackwardRoot5 : CoverTree := .leaf 38 [⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨9,[(1,2),(2,1),(3,36)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target0BackwardRoot5_checked : checkTree [(1,0,18),(-3,1,-18),(-3,-2,-108),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot5 = true := by decide

def target0BackwardRoot6 : CoverTree := .leaf 38 [⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩]
theorem target0BackwardRoot6_checked : checkTree [(0,1,36),(-3,-2,-108),(3,-1,18),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot6 = true := by decide

def target0BackwardRoot7 : CoverTree := .split (-1,-2,-72) (.leaf 38 [⟨4,[(2,3),(4,1),(3,36)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 39 [⟨1,[(4,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨3,[(0,2),(1,1),(3,18)]⟩,⟨3,[(0,1),(1,2),(3,36)]⟩])
theorem target0BackwardRoot7_checked : checkTree [(-3,-1,-72),(3,-1,18),(3,2,108),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot7 = true := by decide

theorem targetMeshFamily0Chunk0_covered : FamilyCover targetMeshFamily0Chunk0 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk0,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot0,target0BackwardRoot0_checked⟩
  · exact ⟨target0BackwardRoot1,target0BackwardRoot1_checked⟩
  · exact ⟨target0BackwardRoot2,target0BackwardRoot2_checked⟩
  · exact ⟨target0BackwardRoot3,target0BackwardRoot3_checked⟩
  · exact ⟨target0BackwardRoot4,target0BackwardRoot4_checked⟩
  · exact ⟨target0BackwardRoot5,target0BackwardRoot5_checked⟩
  · exact ⟨target0BackwardRoot6,target0BackwardRoot6_checked⟩
  · exact ⟨target0BackwardRoot7,target0BackwardRoot7_checked⟩

def target0BackwardRoot8 : CoverTree := .split (1,2,72) (.leaf 39 [⟨1,[(4,1)]⟩,⟨5,[(0,2),(4,1),(3,12)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 38 [⟨9,[(1,5),(2,4),(3,90)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨6,[(0,1),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot8_checked : checkTree [(-3,-1,-72),(6,1,126),(-3,1,-18),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot8 = true := by decide

def target0BackwardRoot9 : CoverTree := .leaf 55 [⟨1,[(1,1)]⟩,⟨3,[(0,1),(2,1),(3,18)]⟩,⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target0BackwardRoot9_checked : checkTree [(2,1,36),(-1,1,72),(-5,-4,-162),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot9 = true := by decide

def target0BackwardRoot10 : CoverTree := .leaf 54 [⟨1,[(0,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(2,1)]⟩]
theorem target0BackwardRoot10_checked : checkTree [(1,2,108),(-4,-5,-234),(1,-1,-72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot10 = true := by decide

def target0BackwardRoot11 : CoverTree := .leaf 54 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(1,1)]⟩]
theorem target0BackwardRoot11_checked : checkTree [(-1,-1,-42),(1,-1,-72),(4,5,234),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot11 = true := by decide

def target0BackwardRoot12 : CoverTree := .leaf 55 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩]
theorem target0BackwardRoot12_checked : checkTree [(-1,-1,-42),(5,4,162),(-1,1,72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot12 = true := by decide

def target0BackwardRoot13 : CoverTree := .split (-1,1,72) (.leaf 55 [⟨1,[(4,1)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 54 [⟨2,[(0,1),(1,1),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot13_checked : checkTree [(1,1,42),(1,3,156),(-5,-6,-258),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot13 = true := by decide

def target0BackwardRoot14 : CoverTree := .leaf 54 [⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨9,[(1,2),(2,1),(3,36)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target0BackwardRoot14_checked : checkTree [(1,1,42),(-4,-3,-102),(-1,-3,-156),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot14 = true := by decide

def target0BackwardRoot15 : CoverTree := .leaf 54 [⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩]
theorem target0BackwardRoot15_checked : checkTree [(-1,0,24),(-1,-3,-156),(4,3,102),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot15 = true := by decide

theorem targetMeshFamily0Chunk1_covered : FamilyCover targetMeshFamily0Chunk1 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk1,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot8,target0BackwardRoot8_checked⟩
  · exact ⟨target0BackwardRoot9,target0BackwardRoot9_checked⟩
  · exact ⟨target0BackwardRoot10,target0BackwardRoot10_checked⟩
  · exact ⟨target0BackwardRoot11,target0BackwardRoot11_checked⟩
  · exact ⟨target0BackwardRoot12,target0BackwardRoot12_checked⟩
  · exact ⟨target0BackwardRoot13,target0BackwardRoot13_checked⟩
  · exact ⟨target0BackwardRoot14,target0BackwardRoot14_checked⟩
  · exact ⟨target0BackwardRoot15,target0BackwardRoot15_checked⟩

def target0BackwardRoot16 : CoverTree := .split (1,-1,-72) (.leaf 54 [⟨4,[(2,3),(4,1),(3,36)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 55 [⟨1,[(4,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨3,[(0,2),(1,1),(3,18)]⟩,⟨3,[(0,1),(1,2),(3,36)]⟩])
theorem target0BackwardRoot16_checked : checkTree [(-2,-3,-132),(4,3,102),(1,3,156),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot16 = true := by decide

def target0BackwardRoot17 : CoverTree := .split (-1,1,72) (.leaf 55 [⟨1,[(4,1)]⟩,⟨5,[(0,2),(4,1),(3,12)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 54 [⟨9,[(1,5),(2,4),(3,90)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨6,[(0,1),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot17_checked : checkTree [(-2,-3,-132),(5,6,258),(-4,-3,-102),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot17 = true := by decide

def target0BackwardRoot18 : CoverTree := .leaf 63 [⟨1,[(1,1)]⟩,⟨3,[(0,1),(2,1),(3,18)]⟩,⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target0BackwardRoot18_checked : checkTree [(1,2,36),(-2,-1,72),(-1,-5,-162),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot18 = true := by decide

def target0BackwardRoot19 : CoverTree := .leaf 62 [⟨1,[(0,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(2,1)]⟩]
theorem target0BackwardRoot19_checked : checkTree [(-1,1,108),(1,-4,-234),(2,1,-72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot19 = true := by decide

def target0BackwardRoot20 : CoverTree := .leaf 62 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(1,1)]⟩]
theorem target0BackwardRoot20_checked : checkTree [(0,-1,-42),(2,1,-72),(-1,4,234),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot20 = true := by decide

def target0BackwardRoot21 : CoverTree := .leaf 63 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩]
theorem target0BackwardRoot21_checked : checkTree [(0,-1,-42),(1,5,162),(-2,-1,72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot21 = true := by decide

def target0BackwardRoot22 : CoverTree := .split (-2,-1,72) (.leaf 63 [⟨1,[(4,1)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 62 [⟨2,[(0,1),(1,1),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot22_checked : checkTree [(0,1,42),(-2,1,156),(1,-5,-258),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot22 = true := by decide

def target0BackwardRoot23 : CoverTree := .leaf 62 [⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨9,[(1,2),(2,1),(3,36)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target0BackwardRoot23_checked : checkTree [(0,1,42),(-1,-4,-102),(2,-1,-156),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot23 = true := by decide

theorem targetMeshFamily0Chunk2_covered : FamilyCover targetMeshFamily0Chunk2 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk2,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot16,target0BackwardRoot16_checked⟩
  · exact ⟨target0BackwardRoot17,target0BackwardRoot17_checked⟩
  · exact ⟨target0BackwardRoot18,target0BackwardRoot18_checked⟩
  · exact ⟨target0BackwardRoot19,target0BackwardRoot19_checked⟩
  · exact ⟨target0BackwardRoot20,target0BackwardRoot20_checked⟩
  · exact ⟨target0BackwardRoot21,target0BackwardRoot21_checked⟩
  · exact ⟨target0BackwardRoot22,target0BackwardRoot22_checked⟩
  · exact ⟨target0BackwardRoot23,target0BackwardRoot23_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
