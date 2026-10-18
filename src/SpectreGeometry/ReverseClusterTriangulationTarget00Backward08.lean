module

public import SpectreGeometry.ReverseClusterTriangulationTarget00Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target0BackwardRoot192 : CoverTree := .split (0,-1,0) (.split (-1,1,36) (.leaf 13 [⟨1,[(5,1)]⟩,⟨5,[(1,1),(4,1),(3,12)]⟩,⟨1,[(4,1)]⟩,⟨2,[(0,1),(2,1)]⟩]) (.leaf 12 [⟨1,[(0,2),(1,3)]⟩,⟨3,[(0,4),(1,7)]⟩,⟨5,[(1,1),(4,1),(3,12)]⟩,⟨1,[(5,1)]⟩])) (.leaf 17 [⟨2,[(0,1),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨4,[(2,1),(4,5),(3,6)]⟩,⟨4,[(0,1),(2,3),(3,36)]⟩])
theorem target0BackwardRoot192_checked : checkTree [(8,7,-162),(-5,-4,108),(-4,-5,90),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot192 = true := by decide

def target0BackwardRoot193 : CoverTree := .split (1,-1,-36) (.leaf 12 [⟨1,[(0,2),(2,1)]⟩,⟨3,[(0,4),(2,1)]⟩,⟨3,[(0,2),(4,1)]⟩,⟨1,[(4,1)]⟩]) (.split (0,-1,0) (.leaf 13 [⟨1,[(4,1)]⟩,⟨9,[(1,1),(2,1),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨3,[(1,1),(2,4),(3,18)]⟩]) (.leaf 17 [⟨3,[(1,1),(2,4),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨14,[(1,1),(5,13),(3,30)]⟩,⟨3,[(1,2),(2,5),(3,36)]⟩]))
theorem target0BackwardRoot193_checked : checkTree [(-2,-1,54),(-14,-13,306),(5,4,-108),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot193 = true := by decide

def target0BackwardRoot194 : CoverTree := .split (-1,1,36) (.split (0,-1,0) (.leaf 13 [⟨1,[(4,1)]⟩,⟨6,[(0,1),(1,1)]⟩,⟨1,[(5,1)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩]) (.leaf 17 [⟨3,[(1,2),(2,1),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨4,[(1,1),(5,5),(3,6)]⟩,⟨6,[(1,5),(2,1),(3,72)]⟩])) (.leaf 12 [⟨4,[(0,5),(2,1),(3,36)]⟩,⟨12,[(0,13),(2,1),(3,36)]⟩,⟨3,[(0,2),(4,1)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot194_checked : checkTree [(-2,-1,54),(-4,-5,90),(14,13,-306),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot194 = true := by decide

def target0BackwardRoot195 : CoverTree := .split (0,1,0) (.leaf 17 [⟨1,[(0,3),(1,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1),(4,1)]⟩,⟨1,[(0,6),(1,1)]⟩]) (.leaf 13 [⟨1,[(0,9),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,3),(1,1)]⟩])
theorem target0BackwardRoot195_checked : checkTree [(-1,-1,24),(5,4,-108),(4,5,-90),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot195 = true := by decide

def target0BackwardRoot196 : CoverTree := .split (1,2,-36) (.split (1,0,0) (.leaf 21 [⟨1,[(0,3),(4,1)]⟩,⟨1,[(0,1),(5,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 25 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,27),(1,2)]⟩])) (.split (2,1,-36) (.leaf 17 [⟨1,[(5,1)]⟩,⟨9,[(1,5),(2,14),(3,18)]⟩,⟨9,[(1,4),(2,13),(3,36)]⟩,⟨1,[(4,1)]⟩]) (.split (1,-1,0) (.leaf 16 [⟨1,[(6,1)]⟩,⟨9,[(1,1),(2,1),(3,90)]⟩,⟨6,[(1,1),(5,7),(3,54)]⟩,⟨1,[(5,1)]⟩]) (.leaf 18 [⟨1,[(4,1)]⟩,⟨15,[(1,2),(4,13),(3,144)]⟩,⟨9,[(1,1),(2,1),(3,90)]⟩,⟨1,[(6,1)]⟩])))
theorem target0BackwardRoot196_checked : checkTree [(-1,-1,24),(14,13,-306),(-5,-4,108),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot196 = true := by decide

def target0BackwardRoot197 : CoverTree := .split (0,-1,24) (.leaf 21 [⟨1,[(1,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1),(4,1)]⟩,⟨1,[(0,3),(1,1)]⟩]) (.leaf 23 [⟨1,[(0,15),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(1,1)]⟩])
theorem target0BackwardRoot197_checked : checkTree [(1,1,-24),(-2,-1,36),(-7,-8,198),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot197 = true := by decide

def target0BackwardRoot198 : CoverTree := .split (-1,-2,36) (.split (-1,0,24) (.leaf 17 [⟨1,[(2,1)]⟩,⟨1,[(0,1),(5,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 15 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,21),(1,2)]⟩])) (.split (-1,1,0) (.leaf 20 [⟨1,[(5,1)]⟩,⟨9,[(1,1),(2,1),(3,90)]⟩,⟨9,[(1,2),(2,11),(3,72)]⟩,⟨1,[(2,1)]⟩]) (.leaf 19 [⟨1,[(4,1)]⟩,⟨6,[(1,1),(4,5),(3,54)]⟩,⟨9,[(1,1),(2,1),(3,90)]⟩,⟨1,[(5,1)]⟩]))
theorem target0BackwardRoot198_checked : checkTree [(1,1,-24),(-11,-10,270),(2,1,-36),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot198 = true := by decide

def target0BackwardRoot199 : CoverTree := .split (-1,-2,36) (.split (-1,0,24) (.leaf 17 [⟨2,[(1,1),(2,1)]⟩,⟨10,[(2,1),(5,11),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 15 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨6,[(0,1),(2,1)]⟩,⟨2,[(0,7),(2,3)]⟩])) (.split (1,-1,0) (.leaf 19 [⟨1,[(4,1)]⟩,⟨3,[(0,1),(4,2),(3,18)]⟩,⟨6,[(1,1),(4,1),(3,54)]⟩,⟨1,[(5,1)]⟩]) (.leaf 20 [⟨1,[(5,1)]⟩,⟨6,[(1,1),(4,1),(3,54)]⟩,⟨18,[(1,11),(2,7),(3,144)]⟩,⟨2,[(1,1),(2,1)]⟩]))
theorem target0BackwardRoot199_checked : checkTree [(-5,-4,126),(-7,-8,198),(11,10,-270),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot199 = true := by decide

theorem targetMeshFamily0Chunk24_covered : FamilyCover targetMeshFamily0Chunk24 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk24,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot192,target0BackwardRoot192_checked⟩
  · exact ⟨target0BackwardRoot193,target0BackwardRoot193_checked⟩
  · exact ⟨target0BackwardRoot194,target0BackwardRoot194_checked⟩
  · exact ⟨target0BackwardRoot195,target0BackwardRoot195_checked⟩
  · exact ⟨target0BackwardRoot196,target0BackwardRoot196_checked⟩
  · exact ⟨target0BackwardRoot197,target0BackwardRoot197_checked⟩
  · exact ⟨target0BackwardRoot198,target0BackwardRoot198_checked⟩
  · exact ⟨target0BackwardRoot199,target0BackwardRoot199_checked⟩

def target0BackwardRoot200 : CoverTree := .split (-1,1,0) (.leaf 20 [⟨1,[(4,1)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨3,[(0,2),(1,5)]⟩,⟨1,[(1,1)]⟩]) (.leaf 19 [⟨2,[(0,1),(2,1)]⟩,⟨3,[(0,2),(2,1),(3,18)]⟩,⟨3,[(0,1),(1,1),(3,18)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot200_checked : checkTree [(-5,-4,126),(2,1,-36),(7,8,-198),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot200 = true := by decide

def target0BackwardRoot201 : CoverTree := .split (0,-1,24) (.leaf 21 [⟨1,[(2,1)]⟩,⟨1,[(4,1)]⟩,⟨6,[(0,5),(1,1)]⟩,⟨3,[(1,1),(2,4),(3,18)]⟩]) (.leaf 23 [⟨4,[(0,7),(1,1),(3,36)]⟩,⟨9,[(1,1),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩,⟨1,[(2,1)]⟩])
theorem target0BackwardRoot201_checked : checkTree [(-1,-2,54),(11,10,-270),(-2,-1,36),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot201 = true := by decide

def target0BackwardRoot202 : CoverTree := .split (0,1,-24) (.leaf 23 [⟨2,[(0,5),(1,1)]⟩,⟨6,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,2),(4,3)]⟩]) (.leaf 21 [⟨2,[(1,1),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨7,[(1,1),(4,8),(3,6)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩])
theorem target0BackwardRoot202_checked : checkTree [(-1,-2,54),(7,8,-198),(-11,-10,270),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot202 = true := by decide

def target0BackwardRoot203 : CoverTree := .leaf 23 [⟨3,[(1,8),(2,1),(3,6)]⟩,⟨3,[(1,2),(2,1),(3,6)]⟩,⟨1,[(0,3),(2,2)]⟩,⟨1,[(0,7),(2,4)]⟩]
theorem target0BackwardRoot203_checked : checkTree [(-2,-3,84),(0,-1,30),(3,5,-138),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot203 = true := by decide

def target0BackwardRoot204 : CoverTree := .split (-1,1,-36) (.leaf 22 [⟨1,[(0,2),(1,1),(3,12)]⟩,⟨1,[(0,4),(1,3)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 23 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,2),(3,12)]⟩])
theorem target0BackwardRoot204_checked : checkTree [(-2,-3,84),(3,4,-108),(0,1,-30),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot204 = true := by decide

def target0BackwardRoot205 : CoverTree := .split (-1,1,-36) (.leaf 22 [⟨1,[(0,2),(2,1),(3,12)]⟩,⟨1,[(0,4),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 23 [⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨3,[(1,5),(2,2),(3,42)]⟩])
theorem target0BackwardRoot205_checked : checkTree [(1,1,-24),(0,1,-30),(-3,-4,108),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot205 = true := by decide

def target0BackwardRoot206 : CoverTree := .leaf 23 [⟨1,[(0,1),(2,3)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨2,[(0,3),(1,1),(3,6)]⟩,⟨2,[(0,5),(1,3),(3,18)]⟩]
theorem target0BackwardRoot206_checked : checkTree [(1,2,-54),(-3,-4,108),(0,-1,30),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot206 = true := by decide

def target0BackwardRoot207 : CoverTree := .leaf 23 [⟨3,[(1,7),(2,8),(3,6)]⟩,⟨3,[(1,1),(2,2),(3,6)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,7),(1,3)]⟩]
theorem target0BackwardRoot207_checked : checkTree [(1,2,-54),(-3,-5,138),(3,4,-108),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot207 = true := by decide

theorem targetMeshFamily0Chunk25_covered : FamilyCover targetMeshFamily0Chunk25 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk25,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot200,target0BackwardRoot200_checked⟩
  · exact ⟨target0BackwardRoot201,target0BackwardRoot201_checked⟩
  · exact ⟨target0BackwardRoot202,target0BackwardRoot202_checked⟩
  · exact ⟨target0BackwardRoot203,target0BackwardRoot203_checked⟩
  · exact ⟨target0BackwardRoot204,target0BackwardRoot204_checked⟩
  · exact ⟨target0BackwardRoot205,target0BackwardRoot205_checked⟩
  · exact ⟨target0BackwardRoot206,target0BackwardRoot206_checked⟩
  · exact ⟨target0BackwardRoot207,target0BackwardRoot207_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
