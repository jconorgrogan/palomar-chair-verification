module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1BackwardRoot0 : CoverTree := .leaf 39 [⟨1,[(1,1)]⟩,⟨3,[(0,1),(2,1),(3,18)]⟩,⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target1BackwardRoot0_checked : checkTree [(1,-1,0),(1,2,72),(-4,1,-54),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot0 = true := by decide

def target1BackwardRoot1 : CoverTree := .leaf 38 [⟨1,[(0,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(2,1)]⟩]
theorem target1BackwardRoot1_checked : checkTree [(2,1,72),(-5,-1,-126),(-1,-2,-72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot1 = true := by decide

def target1BackwardRoot2 : CoverTree := .leaf 38 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(1,1)]⟩]
theorem target1BackwardRoot2_checked : checkTree [(-1,0,-18),(-1,-2,-72),(5,1,126),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot2 = true := by decide

def target1BackwardRoot3 : CoverTree := .leaf 39 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩]
theorem target1BackwardRoot3_checked : checkTree [(-1,0,-18),(4,-1,54),(1,2,72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot3 = true := by decide

def target1BackwardRoot4 : CoverTree := .split (1,2,72) (.leaf 39 [⟨1,[(4,1)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 38 [⟨2,[(0,1),(1,1),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot4_checked : checkTree [(1,0,18),(3,2,108),(-6,-1,-126),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot4 = true := by decide

def target1BackwardRoot5 : CoverTree := .leaf 38 [⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨9,[(1,2),(2,1),(3,36)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target1BackwardRoot5_checked : checkTree [(1,0,18),(-3,1,-18),(-3,-2,-108),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot5 = true := by decide

def target1BackwardRoot6 : CoverTree := .leaf 38 [⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩]
theorem target1BackwardRoot6_checked : checkTree [(0,1,36),(-3,-2,-108),(3,-1,18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot6 = true := by decide

def target1BackwardRoot7 : CoverTree := .split (-1,-2,-72) (.leaf 38 [⟨4,[(2,3),(4,1),(3,36)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 39 [⟨1,[(4,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨3,[(0,2),(1,1),(3,18)]⟩,⟨3,[(0,1),(1,2),(3,36)]⟩])
theorem target1BackwardRoot7_checked : checkTree [(-3,-1,-72),(3,-1,18),(3,2,108),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot7 = true := by decide

theorem targetMeshFamily1Chunk0_covered : FamilyCover targetMeshFamily1Chunk0 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk0,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot0,target1BackwardRoot0_checked⟩
  · exact ⟨target1BackwardRoot1,target1BackwardRoot1_checked⟩
  · exact ⟨target1BackwardRoot2,target1BackwardRoot2_checked⟩
  · exact ⟨target1BackwardRoot3,target1BackwardRoot3_checked⟩
  · exact ⟨target1BackwardRoot4,target1BackwardRoot4_checked⟩
  · exact ⟨target1BackwardRoot5,target1BackwardRoot5_checked⟩
  · exact ⟨target1BackwardRoot6,target1BackwardRoot6_checked⟩
  · exact ⟨target1BackwardRoot7,target1BackwardRoot7_checked⟩

def target1BackwardRoot8 : CoverTree := .split (1,2,72) (.leaf 39 [⟨1,[(4,1)]⟩,⟨5,[(0,2),(4,1),(3,12)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 38 [⟨9,[(1,5),(2,4),(3,90)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨6,[(0,1),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot8_checked : checkTree [(-3,-1,-72),(6,1,126),(-3,1,-18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot8 = true := by decide

def target1BackwardRoot9 : CoverTree := .leaf 55 [⟨1,[(1,1)]⟩,⟨3,[(0,1),(2,1),(3,18)]⟩,⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target1BackwardRoot9_checked : checkTree [(2,1,36),(-1,1,72),(-5,-4,-162),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot9 = true := by decide

def target1BackwardRoot10 : CoverTree := .leaf 54 [⟨1,[(0,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(2,1)]⟩]
theorem target1BackwardRoot10_checked : checkTree [(1,2,108),(-4,-5,-234),(1,-1,-72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot10 = true := by decide

def target1BackwardRoot11 : CoverTree := .leaf 54 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(1,1)]⟩]
theorem target1BackwardRoot11_checked : checkTree [(-1,-1,-42),(1,-1,-72),(4,5,234),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot11 = true := by decide

def target1BackwardRoot12 : CoverTree := .leaf 55 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩]
theorem target1BackwardRoot12_checked : checkTree [(-1,-1,-42),(5,4,162),(-1,1,72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot12 = true := by decide

def target1BackwardRoot13 : CoverTree := .split (-1,1,72) (.leaf 55 [⟨1,[(4,1)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 54 [⟨2,[(0,1),(1,1),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot13_checked : checkTree [(1,1,42),(1,3,156),(-5,-6,-258),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot13 = true := by decide

def target1BackwardRoot14 : CoverTree := .leaf 54 [⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨9,[(1,2),(2,1),(3,36)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target1BackwardRoot14_checked : checkTree [(1,1,42),(-4,-3,-102),(-1,-3,-156),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot14 = true := by decide

def target1BackwardRoot15 : CoverTree := .leaf 54 [⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨3,[(0,2),(1,1)]⟩,⟨9,[(1,7),(2,4),(3,36)]⟩]
theorem target1BackwardRoot15_checked : checkTree [(-1,0,24),(-1,-3,-156),(4,3,102),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot15 = true := by decide

theorem targetMeshFamily1Chunk1_covered : FamilyCover targetMeshFamily1Chunk1 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk1,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot8,target1BackwardRoot8_checked⟩
  · exact ⟨target1BackwardRoot9,target1BackwardRoot9_checked⟩
  · exact ⟨target1BackwardRoot10,target1BackwardRoot10_checked⟩
  · exact ⟨target1BackwardRoot11,target1BackwardRoot11_checked⟩
  · exact ⟨target1BackwardRoot12,target1BackwardRoot12_checked⟩
  · exact ⟨target1BackwardRoot13,target1BackwardRoot13_checked⟩
  · exact ⟨target1BackwardRoot14,target1BackwardRoot14_checked⟩
  · exact ⟨target1BackwardRoot15,target1BackwardRoot15_checked⟩

def target1BackwardRoot16 : CoverTree := .split (1,-1,-72) (.leaf 54 [⟨4,[(2,3),(4,1),(3,36)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 55 [⟨1,[(4,1)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨3,[(0,2),(1,1),(3,18)]⟩,⟨3,[(0,1),(1,2),(3,36)]⟩])
theorem target1BackwardRoot16_checked : checkTree [(-2,-3,-132),(4,3,102),(1,3,156),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot16 = true := by decide

def target1BackwardRoot17 : CoverTree := .split (-1,1,72) (.leaf 55 [⟨1,[(4,1)]⟩,⟨5,[(0,2),(4,1),(3,12)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 54 [⟨9,[(1,5),(2,4),(3,90)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨6,[(0,1),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot17_checked : checkTree [(-2,-3,-132),(5,6,258),(-4,-3,-102),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot17 = true := by decide

def target1BackwardRoot18 : CoverTree := .leaf 63 [⟨1,[(1,1)]⟩,⟨3,[(0,1),(2,1),(3,18)]⟩,⟨3,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target1BackwardRoot18_checked : checkTree [(1,2,36),(-2,-1,72),(-1,-5,-162),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot18 = true := by decide

def target1BackwardRoot19 : CoverTree := .leaf 62 [⟨1,[(0,1)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(2,1)]⟩]
theorem target1BackwardRoot19_checked : checkTree [(-1,1,108),(1,-4,-234),(2,1,-72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot19 = true := by decide

def target1BackwardRoot20 : CoverTree := .leaf 62 [⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(1,1)]⟩]
theorem target1BackwardRoot20_checked : checkTree [(0,-1,-42),(2,1,-72),(-1,4,234),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot20 = true := by decide

def target1BackwardRoot21 : CoverTree := .leaf 63 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩]
theorem target1BackwardRoot21_checked : checkTree [(0,-1,-42),(1,5,162),(-2,-1,72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot21 = true := by decide

def target1BackwardRoot22 : CoverTree := .split (-2,-1,72) (.leaf 63 [⟨1,[(4,1)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(0,5),(2,1)]⟩,⟨1,[(0,7),(2,1)]⟩]) (.leaf 62 [⟨2,[(0,1),(1,1),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩,⟨9,[(1,1),(2,2),(3,36)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot22_checked : checkTree [(0,1,42),(-2,1,156),(1,-5,-258),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot22 = true := by decide

def target1BackwardRoot23 : CoverTree := .leaf 62 [⟨1,[(0,5),(1,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨9,[(1,2),(2,1),(3,36)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target1BackwardRoot23_checked : checkTree [(0,1,42),(-1,-4,-102),(2,-1,-156),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot23 = true := by decide

theorem targetMeshFamily1Chunk2_covered : FamilyCover targetMeshFamily1Chunk2 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk2,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot16,target1BackwardRoot16_checked⟩
  · exact ⟨target1BackwardRoot17,target1BackwardRoot17_checked⟩
  · exact ⟨target1BackwardRoot18,target1BackwardRoot18_checked⟩
  · exact ⟨target1BackwardRoot19,target1BackwardRoot19_checked⟩
  · exact ⟨target1BackwardRoot20,target1BackwardRoot20_checked⟩
  · exact ⟨target1BackwardRoot21,target1BackwardRoot21_checked⟩
  · exact ⟨target1BackwardRoot22,target1BackwardRoot22_checked⟩
  · exact ⟨target1BackwardRoot23,target1BackwardRoot23_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
