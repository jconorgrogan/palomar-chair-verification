module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1BackwardRoot48 : CoverTree := .leaf 27 [⟨1,[(0,2),(1,1)]⟩,⟨3,[(1,1),(2,4),(3,12)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩]
theorem target1BackwardRoot48_checked : checkTree [(-1,0,-24),(3,-1,84),(0,1,-6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot48 = true := by decide

def target1BackwardRoot49 : CoverTree := .split (1,2,72) (.leaf 39 [⟨1,[(4,1)]⟩,⟨2,[(1,1),(2,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,5),(2,2)]⟩]) (.leaf 38 [⟨4,[(0,1),(1,1),(3,60)]⟩,⟨6,[(1,7),(2,5),(3,24)]⟩,⟨2,[(1,1),(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot49_checked : checkTree [(3,1,72),(5,3,156),(-7,-3,-180),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot49 = true := by decide

def target1BackwardRoot50 : CoverTree := .split (-1,-2,-72) (.leaf 38 [⟨1,[(0,1),(1,1),(3,12)]⟩,⟨1,[(0,1),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 39 [⟨1,[(4,1)]⟩,⟨1,[(1,1)]⟩,⟨2,[(0,1),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1),(3,12)]⟩])
theorem target1BackwardRoot50_checked : checkTree [(3,1,72),(-1,0,-12),(-5,-3,-156),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot50 = true := by decide

def target1BackwardRoot51 : CoverTree := .leaf 51 [⟨3,[(1,2),(2,7),(3,12)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,4),(1,1)]⟩]
theorem target1BackwardRoot51_checked : checkTree [(1,1,48),(-5,-3,-156),(1,0,12),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot51 = true := by decide

def target1BackwardRoot52 : CoverTree := .leaf 51 [⟨1,[(0,2),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,8),(2,3)]⟩]
theorem target1BackwardRoot52_checked : checkTree [(-2,-1,-54),(1,0,12),(5,3,156),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot52 = true := by decide

def target1BackwardRoot53 : CoverTree := .split (1,2,72) (.leaf 39 [⟨1,[(4,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,4),(1,1)]⟩,⟨1,[(0,10),(1,3)]⟩]) (.leaf 38 [⟨3,[(1,1),(2,1),(3,48)]⟩,⟨3,[(1,1),(2,7),(3,12)]⟩,⟨1,[(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot53_checked : checkTree [(-2,-1,-54),(7,3,180),(-1,0,-12),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot53 = true := by decide

def target1BackwardRoot54 : CoverTree := .split (-1,0,-12) (.leaf 39 [⟨1,[(0,2),(4,3)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,4),(2,1)]⟩,⟨1,[(0,14),(2,3)]⟩]) (.split (-1,-2,-72) (.leaf 51 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨3,[(1,4),(2,1),(3,12)]⟩,⟨3,[(1,14),(2,5),(3,24)]⟩]) (.leaf 41 [⟨3,[(1,1),(2,1),(3,48)]⟩,⟨5,[(2,1),(4,9),(3,24)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot54_checked : checkTree [(2,1,54),(3,2,96),(-9,-5,-252),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot54 = true := by decide

def target1BackwardRoot55 : CoverTree := .leaf 51 [⟨1,[(0,4),(2,3)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(0,4),(1,3)]⟩]
theorem target1BackwardRoot55_checked : checkTree [(2,1,54),(-3,-1,-60),(-3,-2,-96),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot55 = true := by decide

theorem targetMeshFamily1Chunk6_covered : FamilyCover targetMeshFamily1Chunk6 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk6,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot48,target1BackwardRoot48_checked⟩
  · exact ⟨target1BackwardRoot49,target1BackwardRoot49_checked⟩
  · exact ⟨target1BackwardRoot50,target1BackwardRoot50_checked⟩
  · exact ⟨target1BackwardRoot51,target1BackwardRoot51_checked⟩
  · exact ⟨target1BackwardRoot52,target1BackwardRoot52_checked⟩
  · exact ⟨target1BackwardRoot53,target1BackwardRoot53_checked⟩
  · exact ⟨target1BackwardRoot54,target1BackwardRoot54_checked⟩
  · exact ⟨target1BackwardRoot55,target1BackwardRoot55_checked⟩

def target1BackwardRoot56 : CoverTree := .split (1,-1,-36) (.leaf 52 [⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,1),(1,1),(3,12)]⟩]) (.leaf 51 [⟨3,[(1,5),(2,4),(3,24)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot56_checked : checkTree [(1,1,48),(-3,-2,-96),(3,1,60),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot56 = true := by decide

def target1BackwardRoot57 : CoverTree := .split (-1,1,36) (.leaf 51 [⟨4,[(0,5),(1,7),(3,12)]⟩,⟨4,[(0,1),(1,3),(3,12)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨1,[(4,1)]⟩]) (.leaf 52 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,3),(2,5)]⟩,⟨1,[(0,1),(2,1),(3,12)]⟩])
theorem target1BackwardRoot57_checked : checkTree [(-5,-3,-144),(3,1,60),(3,2,96),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot57 = true := by decide

def target1BackwardRoot58 : CoverTree := .split (1,2,72) (.split (-1,0,-12) (.leaf 39 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(0,7),(1,4)]⟩]) (.leaf 41 [⟨1,[(2,1),(5,1),(3,12)]⟩,⟨1,[(2,1),(5,3)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.leaf 51 [⟨1,[(4,1)]⟩,⟨13,[(1,2),(4,5),(3,12)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩,⟨3,[(1,2),(2,7),(3,24)]⟩])
theorem target1BackwardRoot58_checked : checkTree [(-5,-3,-144),(9,5,252),(-3,-1,-60),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot58 = true := by decide

def target1BackwardRoot59 : CoverTree := .split (1,2,72) (.split (-1,0,-12) (.leaf 39 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,3),(2,2)]⟩,⟨5,[(0,17),(2,8)]⟩]) (.leaf 41 [⟨3,[(1,4),(2,1),(3,30)]⟩,⟨7,[(2,1),(5,10),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.leaf 51 [⟨1,[(4,1)]⟩,⟨1,[(1,2),(4,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨3,[(1,17),(2,2),(3,6)]⟩])
theorem target1BackwardRoot59_checked : checkTree [(5,3,144),(1,1,42),(-10,-7,-306),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot59 = true := by decide

def target1BackwardRoot60 : CoverTree := .split (-1,1,36) (.leaf 51 [⟨2,[(0,1),(2,7),(3,6)]⟩,⟨2,[(0,1),(2,3),(3,6)]⟩,⟨4,[(0,1),(4,1),(3,12)]⟩,⟨1,[(4,1)]⟩]) (.leaf 52 [⟨1,[(4,1)]⟩,⟨5,[(0,3),(1,2)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨3,[(1,1),(2,1),(3,30)]⟩])
theorem target1BackwardRoot60_checked : checkTree [(5,3,144),(-5,-2,-96),(-1,-1,-42),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot60 = true := by decide

def target1BackwardRoot61 : CoverTree := .split (1,-1,-36) (.leaf 52 [⟨1,[(4,1)]⟩,⟨5,[(0,3),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩]) (.leaf 51 [⟨3,[(1,8),(2,1),(3,24)]⟩,⟨3,[(1,2),(2,1),(3,24)]⟩,⟨5,[(0,3),(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot61_checked : checkTree [(0,1,48),(-1,-1,-42),(5,2,96),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot61 = true := by decide

def target1BackwardRoot62 : CoverTree := .split (1,-1,-36) (.leaf 52 [⟨1,[(4,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,5)]⟩,⟨1,[(0,1),(2,3)]⟩]) (.leaf 51 [⟨5,[(0,4),(1,3)]⟩,⟨5,[(0,1),(1,2),(3,30)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot62_checked : checkTree [(-5,-4,-162),(5,2,96),(1,1,42),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot62 = true := by decide

def target1BackwardRoot63 : CoverTree := .split (1,2,72) (.split (1,0,12) (.leaf 41 [⟨2,[(0,1),(4,1),(3,18)]⟩,⟨4,[(0,1),(5,5),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 39 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,3),(1,1)]⟩,⟨5,[(0,17),(1,9)]⟩])) (.leaf 51 [⟨1,[(4,1)]⟩,⟨13,[(1,2),(4,7),(3,48)]⟩,⟨5,[(1,1),(2,1),(3,30)]⟩,⟨15,[(1,7),(2,17),(3,30)]⟩])
theorem target1BackwardRoot63_checked : checkTree [(-5,-4,-162),(10,7,306),(-5,-2,-96),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot63 = true := by decide

theorem targetMeshFamily1Chunk7_covered : FamilyCover targetMeshFamily1Chunk7 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk7,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot56,target1BackwardRoot56_checked⟩
  · exact ⟨target1BackwardRoot57,target1BackwardRoot57_checked⟩
  · exact ⟨target1BackwardRoot58,target1BackwardRoot58_checked⟩
  · exact ⟨target1BackwardRoot59,target1BackwardRoot59_checked⟩
  · exact ⟨target1BackwardRoot60,target1BackwardRoot60_checked⟩
  · exact ⟨target1BackwardRoot61,target1BackwardRoot61_checked⟩
  · exact ⟨target1BackwardRoot62,target1BackwardRoot62_checked⟩
  · exact ⟨target1BackwardRoot63,target1BackwardRoot63_checked⟩

def target1BackwardRoot64 : CoverTree := .leaf 46 [⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨2,[(0,5),(2,3)]⟩]
theorem target1BackwardRoot64_checked : checkTree [(1,2,72),(-1,-1,-18),(-1,-4,-168),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot64 = true := by decide

def target1BackwardRoot65 : CoverTree := .leaf 46 [⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨2,[(0,3),(1,1)]⟩,⟨3,[(1,2),(2,1),(3,30)]⟩]
theorem target1BackwardRoot65_checked : checkTree [(-1,0,36),(1,-2,-132),(1,1,18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot65 = true := by decide

def target1BackwardRoot66 : CoverTree := .leaf 46 [⟨3,[(1,4),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,2),(1,1),(3,6)]⟩]
theorem target1BackwardRoot66_checked : checkTree [(0,-1,-48),(1,1,18),(-1,2,132),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot66 = true := by decide

def target1BackwardRoot67 : CoverTree := .leaf 46 [⟨1,[(0,2),(1,1)]⟩,⟨3,[(1,1),(2,4),(3,12)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩]
theorem target1BackwardRoot67_checked : checkTree [(0,-1,-48),(1,4,168),(-1,-1,-18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot67 = true := by decide

def target1BackwardRoot68 : CoverTree := .split (-2,-1,72) (.leaf 63 [⟨1,[(4,1)]⟩,⟨2,[(1,1),(2,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,5),(2,2)]⟩]) (.leaf 62 [⟨4,[(0,1),(1,1),(3,60)]⟩,⟨6,[(1,7),(2,5),(3,24)]⟩,⟨2,[(1,1),(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot68_checked : checkTree [(-1,2,132),(-3,2,240),(3,-4,-312),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot68 = true := by decide

def target1BackwardRoot69 : CoverTree := .split (2,1,-72) (.leaf 62 [⟨1,[(0,1),(1,1),(3,12)]⟩,⟨1,[(0,1),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 63 [⟨1,[(4,1)]⟩,⟨1,[(1,1)]⟩,⟨2,[(0,1),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1),(3,12)]⟩])
theorem target1BackwardRoot69_checked : checkTree [(-1,2,132),(0,-1,-36),(3,-2,-240),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot69 = true := by decide

def target1BackwardRoot70 : CoverTree := .leaf 67 [⟨3,[(1,2),(2,7),(3,12)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,4),(1,1)]⟩]
theorem target1BackwardRoot70_checked : checkTree [(-1,0,60),(3,-2,-240),(0,1,36),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot70 = true := by decide

def target1BackwardRoot71 : CoverTree := .leaf 67 [⟨1,[(0,2),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,8),(2,3)]⟩]
theorem target1BackwardRoot71_checked : checkTree [(1,-1,-90),(0,1,36),(-3,2,240),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot71 = true := by decide

theorem targetMeshFamily1Chunk8_covered : FamilyCover targetMeshFamily1Chunk8 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk8,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot64,target1BackwardRoot64_checked⟩
  · exact ⟨target1BackwardRoot65,target1BackwardRoot65_checked⟩
  · exact ⟨target1BackwardRoot66,target1BackwardRoot66_checked⟩
  · exact ⟨target1BackwardRoot67,target1BackwardRoot67_checked⟩
  · exact ⟨target1BackwardRoot68,target1BackwardRoot68_checked⟩
  · exact ⟨target1BackwardRoot69,target1BackwardRoot69_checked⟩
  · exact ⟨target1BackwardRoot70,target1BackwardRoot70_checked⟩
  · exact ⟨target1BackwardRoot71,target1BackwardRoot71_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
