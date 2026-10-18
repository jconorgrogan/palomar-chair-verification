module

public import SpectreGeometry.ReverseClusterTriangulationTarget00Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target0BackwardRoot48 : CoverTree := .split (1,-1,36) (.leaf 23 [⟨1,[(4,1)]⟩,⟨5,[(0,2),(4,1),(3,12)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 22 [⟨9,[(1,5),(2,4),(3,90)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨6,[(0,1),(2,1),(3,18)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot48_checked : checkTree [(2,3,-84),(-5,-6,174),(4,3,-78),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot48 = true := by decide

def target0BackwardRoot49 : CoverTree := .leaf 27 [⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨2,[(0,5),(2,3)]⟩]
theorem target0BackwardRoot49_checked : checkTree [(1,-1,36),(0,1,-6),(-3,1,-84),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot49 = true := by decide

def target0BackwardRoot50 : CoverTree := .leaf 27 [⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨2,[(0,3),(1,1)]⟩,⟨3,[(1,2),(2,1),(3,30)]⟩]
theorem target0BackwardRoot50_checked : checkTree [(1,1,24),(-3,-1,-72),(0,-1,6),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot50 = true := by decide

def target0BackwardRoot51 : CoverTree := .leaf 27 [⟨3,[(1,4),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,2),(1,1),(3,6)]⟩]
theorem target0BackwardRoot51_checked : checkTree [(-1,0,-24),(0,-1,6),(3,1,72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot51 = true := by decide

def target0BackwardRoot52 : CoverTree := .leaf 27 [⟨1,[(0,2),(1,1)]⟩,⟨3,[(1,1),(2,4),(3,12)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩]
theorem target0BackwardRoot52_checked : checkTree [(-1,0,-24),(3,-1,84),(0,1,-6),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot52 = true := by decide

def target0BackwardRoot53 : CoverTree := .split (1,2,72) (.leaf 39 [⟨1,[(4,1)]⟩,⟨2,[(1,1),(2,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,5),(2,2)]⟩]) (.leaf 38 [⟨4,[(0,1),(1,1),(3,60)]⟩,⟨6,[(1,7),(2,5),(3,24)]⟩,⟨2,[(1,1),(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot53_checked : checkTree [(3,1,72),(5,3,156),(-7,-3,-180),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot53 = true := by decide

def target0BackwardRoot54 : CoverTree := .split (-1,-2,-72) (.leaf 38 [⟨1,[(0,1),(1,1),(3,12)]⟩,⟨1,[(0,1),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 39 [⟨1,[(4,1)]⟩,⟨1,[(1,1)]⟩,⟨2,[(0,1),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1),(3,12)]⟩])
theorem target0BackwardRoot54_checked : checkTree [(3,1,72),(-1,0,-12),(-5,-3,-156),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot54 = true := by decide

def target0BackwardRoot55 : CoverTree := .leaf 51 [⟨3,[(1,2),(2,7),(3,12)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,4),(1,1)]⟩]
theorem target0BackwardRoot55_checked : checkTree [(1,1,48),(-5,-3,-156),(1,0,12),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot55 = true := by decide

theorem targetMeshFamily0Chunk6_covered : FamilyCover targetMeshFamily0Chunk6 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk6,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot48,target0BackwardRoot48_checked⟩
  · exact ⟨target0BackwardRoot49,target0BackwardRoot49_checked⟩
  · exact ⟨target0BackwardRoot50,target0BackwardRoot50_checked⟩
  · exact ⟨target0BackwardRoot51,target0BackwardRoot51_checked⟩
  · exact ⟨target0BackwardRoot52,target0BackwardRoot52_checked⟩
  · exact ⟨target0BackwardRoot53,target0BackwardRoot53_checked⟩
  · exact ⟨target0BackwardRoot54,target0BackwardRoot54_checked⟩
  · exact ⟨target0BackwardRoot55,target0BackwardRoot55_checked⟩

def target0BackwardRoot56 : CoverTree := .leaf 51 [⟨1,[(0,2),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,8),(2,3)]⟩]
theorem target0BackwardRoot56_checked : checkTree [(-2,-1,-54),(1,0,12),(5,3,156),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot56 = true := by decide

def target0BackwardRoot57 : CoverTree := .split (1,2,72) (.leaf 39 [⟨1,[(4,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,4),(1,1)]⟩,⟨1,[(0,10),(1,3)]⟩]) (.leaf 38 [⟨3,[(1,1),(2,1),(3,48)]⟩,⟨3,[(1,1),(2,7),(3,12)]⟩,⟨1,[(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot57_checked : checkTree [(-2,-1,-54),(7,3,180),(-1,0,-12),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot57 = true := by decide

def target0BackwardRoot58 : CoverTree := .split (-1,0,-12) (.leaf 39 [⟨1,[(0,2),(4,3)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,4),(2,1)]⟩,⟨1,[(0,14),(2,3)]⟩]) (.split (-1,-2,-72) (.leaf 51 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨3,[(1,4),(2,1),(3,12)]⟩,⟨3,[(1,14),(2,5),(3,24)]⟩]) (.leaf 41 [⟨3,[(1,1),(2,1),(3,48)]⟩,⟨5,[(2,1),(4,9),(3,24)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]))
theorem target0BackwardRoot58_checked : checkTree [(2,1,54),(3,2,96),(-9,-5,-252),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot58 = true := by decide

def target0BackwardRoot59 : CoverTree := .leaf 51 [⟨1,[(0,4),(2,3)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(0,4),(1,3)]⟩]
theorem target0BackwardRoot59_checked : checkTree [(2,1,54),(-3,-1,-60),(-3,-2,-96),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot59 = true := by decide

def target0BackwardRoot60 : CoverTree := .split (1,-1,-36) (.leaf 52 [⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,1),(1,1),(3,12)]⟩]) (.leaf 51 [⟨3,[(1,5),(2,4),(3,24)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot60_checked : checkTree [(1,1,48),(-3,-2,-96),(3,1,60),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot60 = true := by decide

def target0BackwardRoot61 : CoverTree := .split (-1,1,36) (.leaf 51 [⟨4,[(0,5),(1,7),(3,12)]⟩,⟨4,[(0,1),(1,3),(3,12)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨1,[(4,1)]⟩]) (.leaf 52 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,3),(2,5)]⟩,⟨1,[(0,1),(2,1),(3,12)]⟩])
theorem target0BackwardRoot61_checked : checkTree [(-5,-3,-144),(3,1,60),(3,2,96),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot61 = true := by decide

def target0BackwardRoot62 : CoverTree := .split (1,2,72) (.split (-1,0,-12) (.leaf 39 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(0,7),(1,4)]⟩]) (.leaf 41 [⟨1,[(2,1),(5,1),(3,12)]⟩,⟨1,[(2,1),(5,3)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.leaf 51 [⟨1,[(4,1)]⟩,⟨13,[(1,2),(4,5),(3,12)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩,⟨3,[(1,2),(2,7),(3,24)]⟩])
theorem target0BackwardRoot62_checked : checkTree [(-5,-3,-144),(9,5,252),(-3,-1,-60),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot62 = true := by decide

def target0BackwardRoot63 : CoverTree := .split (1,2,72) (.split (-1,0,-12) (.leaf 39 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,3),(2,2)]⟩,⟨5,[(0,17),(2,8)]⟩]) (.leaf 41 [⟨3,[(1,4),(2,1),(3,30)]⟩,⟨7,[(2,1),(5,10),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.leaf 51 [⟨1,[(4,1)]⟩,⟨1,[(1,2),(4,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨3,[(1,17),(2,2),(3,6)]⟩])
theorem target0BackwardRoot63_checked : checkTree [(5,3,144),(1,1,42),(-10,-7,-306),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot63 = true := by decide

theorem targetMeshFamily0Chunk7_covered : FamilyCover targetMeshFamily0Chunk7 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk7,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot56,target0BackwardRoot56_checked⟩
  · exact ⟨target0BackwardRoot57,target0BackwardRoot57_checked⟩
  · exact ⟨target0BackwardRoot58,target0BackwardRoot58_checked⟩
  · exact ⟨target0BackwardRoot59,target0BackwardRoot59_checked⟩
  · exact ⟨target0BackwardRoot60,target0BackwardRoot60_checked⟩
  · exact ⟨target0BackwardRoot61,target0BackwardRoot61_checked⟩
  · exact ⟨target0BackwardRoot62,target0BackwardRoot62_checked⟩
  · exact ⟨target0BackwardRoot63,target0BackwardRoot63_checked⟩

def target0BackwardRoot64 : CoverTree := .split (-1,1,36) (.leaf 51 [⟨2,[(0,1),(2,7),(3,6)]⟩,⟨2,[(0,1),(2,3),(3,6)]⟩,⟨4,[(0,1),(4,1),(3,12)]⟩,⟨1,[(4,1)]⟩]) (.leaf 52 [⟨1,[(4,1)]⟩,⟨5,[(0,3),(1,2)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨3,[(1,1),(2,1),(3,30)]⟩])
theorem target0BackwardRoot64_checked : checkTree [(5,3,144),(-5,-2,-96),(-1,-1,-42),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot64 = true := by decide

def target0BackwardRoot65 : CoverTree := .split (1,-1,-36) (.leaf 52 [⟨1,[(4,1)]⟩,⟨5,[(0,3),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩]) (.leaf 51 [⟨3,[(1,8),(2,1),(3,24)]⟩,⟨3,[(1,2),(2,1),(3,24)]⟩,⟨5,[(0,3),(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot65_checked : checkTree [(0,1,48),(-1,-1,-42),(5,2,96),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot65 = true := by decide

def target0BackwardRoot66 : CoverTree := .split (1,-1,-36) (.leaf 52 [⟨1,[(4,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,5)]⟩,⟨1,[(0,1),(2,3)]⟩]) (.leaf 51 [⟨5,[(0,4),(1,3)]⟩,⟨5,[(0,1),(1,2),(3,30)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot66_checked : checkTree [(-5,-4,-162),(5,2,96),(1,1,42),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot66 = true := by decide

def target0BackwardRoot67 : CoverTree := .split (1,2,72) (.split (1,0,12) (.leaf 41 [⟨2,[(0,1),(4,1),(3,18)]⟩,⟨4,[(0,1),(5,5),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 39 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,3),(1,1)]⟩,⟨5,[(0,17),(1,9)]⟩])) (.leaf 51 [⟨1,[(4,1)]⟩,⟨13,[(1,2),(4,7),(3,48)]⟩,⟨5,[(1,1),(2,1),(3,30)]⟩,⟨15,[(1,7),(2,17),(3,30)]⟩])
theorem target0BackwardRoot67_checked : checkTree [(-5,-4,-162),(10,7,306),(-5,-2,-96),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot67 = true := by decide

def target0BackwardRoot68 : CoverTree := .leaf 46 [⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨2,[(0,5),(2,3)]⟩]
theorem target0BackwardRoot68_checked : checkTree [(1,2,72),(-1,-1,-18),(-1,-4,-168),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot68 = true := by decide

def target0BackwardRoot69 : CoverTree := .leaf 46 [⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨2,[(0,3),(1,1)]⟩,⟨3,[(1,2),(2,1),(3,30)]⟩]
theorem target0BackwardRoot69_checked : checkTree [(-1,0,36),(1,-2,-132),(1,1,18),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot69 = true := by decide

def target0BackwardRoot70 : CoverTree := .leaf 46 [⟨3,[(1,4),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,2),(1,1),(3,6)]⟩]
theorem target0BackwardRoot70_checked : checkTree [(0,-1,-48),(1,1,18),(-1,2,132),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot70 = true := by decide

def target0BackwardRoot71 : CoverTree := .leaf 46 [⟨1,[(0,2),(1,1)]⟩,⟨3,[(1,1),(2,4),(3,12)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩]
theorem target0BackwardRoot71_checked : checkTree [(0,-1,-48),(1,4,168),(-1,-1,-18),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot71 = true := by decide

theorem targetMeshFamily0Chunk8_covered : FamilyCover targetMeshFamily0Chunk8 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk8,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot64,target0BackwardRoot64_checked⟩
  · exact ⟨target0BackwardRoot65,target0BackwardRoot65_checked⟩
  · exact ⟨target0BackwardRoot66,target0BackwardRoot66_checked⟩
  · exact ⟨target0BackwardRoot67,target0BackwardRoot67_checked⟩
  · exact ⟨target0BackwardRoot68,target0BackwardRoot68_checked⟩
  · exact ⟨target0BackwardRoot69,target0BackwardRoot69_checked⟩
  · exact ⟨target0BackwardRoot70,target0BackwardRoot70_checked⟩
  · exact ⟨target0BackwardRoot71,target0BackwardRoot71_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
