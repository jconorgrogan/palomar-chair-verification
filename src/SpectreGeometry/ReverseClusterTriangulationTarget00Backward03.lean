module

public import SpectreGeometry.ReverseClusterTriangulationTarget00Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target0BackwardRoot72 : CoverTree := .split (-1,-2,36) (.leaf 15 [⟨1,[(4,1)]⟩,⟨2,[(1,1),(2,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,5),(2,2)]⟩]) (.leaf 14 [⟨4,[(0,1),(1,1),(3,60)]⟩,⟨6,[(1,7),(2,5),(3,24)]⟩,⟨2,[(1,1),(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot72_checked : checkTree [(-3,-1,84),(-5,-3,144),(7,3,-192),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot72 = true := by decide

def target0BackwardRoot73 : CoverTree := .split (1,2,-36) (.leaf 14 [⟨1,[(0,1),(1,1),(3,12)]⟩,⟨1,[(0,1),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 15 [⟨1,[(4,1)]⟩,⟨1,[(1,1)]⟩,⟨2,[(0,1),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1),(3,12)]⟩])
theorem target0BackwardRoot73_checked : checkTree [(-3,-1,84),(1,0,-24),(5,3,-144),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot73 = true := by decide

def target0BackwardRoot74 : CoverTree := .leaf 19 [⟨3,[(1,2),(2,7),(3,12)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,4),(1,1)]⟩]
theorem target0BackwardRoot74_checked : checkTree [(-1,-1,36),(5,3,-144),(-1,0,24),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot74 = true := by decide

def target0BackwardRoot75 : CoverTree := .leaf 19 [⟨1,[(0,2),(1,3)]⟩,⟨1,[(1,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,8),(2,3)]⟩]
theorem target0BackwardRoot75_checked : checkTree [(2,1,-54),(-1,0,24),(-5,-3,144),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot75 = true := by decide

def target0BackwardRoot76 : CoverTree := .split (-1,-2,36) (.leaf 15 [⟨1,[(4,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,4),(1,1)]⟩,⟨1,[(0,10),(1,3)]⟩]) (.leaf 14 [⟨3,[(1,1),(2,1),(3,48)]⟩,⟨3,[(1,1),(2,7),(3,12)]⟩,⟨1,[(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot76_checked : checkTree [(2,1,-54),(-7,-3,192),(1,0,-24),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot76 = true := by decide

def target0BackwardRoot77 : CoverTree := .split (1,0,-24) (.leaf 15 [⟨1,[(0,2),(4,3)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,4),(2,1)]⟩,⟨1,[(0,14),(2,3)]⟩]) (.split (1,2,-36) (.leaf 19 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨3,[(1,4),(2,1),(3,12)]⟩,⟨3,[(1,14),(2,5),(3,24)]⟩]) (.leaf 17 [⟨3,[(1,1),(2,1),(3,48)]⟩,⟨5,[(2,1),(4,9),(3,24)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]))
theorem target0BackwardRoot77_checked : checkTree [(-2,-1,54),(-3,-2,84),(9,5,-240),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot77 = true := by decide

def target0BackwardRoot78 : CoverTree := .leaf 19 [⟨1,[(0,4),(2,3)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(0,4),(1,3)]⟩]
theorem target0BackwardRoot78_checked : checkTree [(-2,-1,54),(3,1,-72),(3,2,-84),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot78 = true := by decide

def target0BackwardRoot79 : CoverTree := .split (-1,1,0) (.leaf 20 [⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,1),(1,1),(3,12)]⟩]) (.leaf 19 [⟨3,[(1,5),(2,4),(3,24)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot79_checked : checkTree [(-1,-1,36),(3,2,-84),(-3,-1,72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot79 = true := by decide

theorem targetMeshFamily0Chunk9_covered : FamilyCover targetMeshFamily0Chunk9 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk9,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot72,target0BackwardRoot72_checked⟩
  · exact ⟨target0BackwardRoot73,target0BackwardRoot73_checked⟩
  · exact ⟨target0BackwardRoot74,target0BackwardRoot74_checked⟩
  · exact ⟨target0BackwardRoot75,target0BackwardRoot75_checked⟩
  · exact ⟨target0BackwardRoot76,target0BackwardRoot76_checked⟩
  · exact ⟨target0BackwardRoot77,target0BackwardRoot77_checked⟩
  · exact ⟨target0BackwardRoot78,target0BackwardRoot78_checked⟩
  · exact ⟨target0BackwardRoot79,target0BackwardRoot79_checked⟩

def target0BackwardRoot80 : CoverTree := .split (1,-1,0) (.leaf 19 [⟨4,[(0,5),(1,7),(3,12)]⟩,⟨4,[(0,1),(1,3),(3,12)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨1,[(4,1)]⟩]) (.leaf 20 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,3),(2,5)]⟩,⟨1,[(0,1),(2,1),(3,12)]⟩])
theorem target0BackwardRoot80_checked : checkTree [(5,3,-132),(-3,-1,72),(-3,-2,84),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot80 = true := by decide

def target0BackwardRoot81 : CoverTree := .split (-1,-2,36) (.split (1,0,-24) (.leaf 15 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(0,7),(1,4)]⟩]) (.leaf 17 [⟨1,[(2,1),(5,1),(3,12)]⟩,⟨1,[(2,1),(5,3)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.leaf 19 [⟨1,[(4,1)]⟩,⟨13,[(1,2),(4,5),(3,12)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩,⟨3,[(1,2),(2,7),(3,24)]⟩])
theorem target0BackwardRoot81_checked : checkTree [(5,3,-132),(-9,-5,240),(3,1,-72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot81 = true := by decide

def target0BackwardRoot82 : CoverTree := .split (-1,-2,36) (.split (1,0,-24) (.leaf 15 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,3),(2,2)]⟩,⟨5,[(0,17),(2,8)]⟩]) (.leaf 17 [⟨3,[(1,4),(2,1),(3,30)]⟩,⟨7,[(2,1),(5,10),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.leaf 19 [⟨1,[(4,1)]⟩,⟨1,[(1,2),(4,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨3,[(1,17),(2,2),(3,6)]⟩])
theorem target0BackwardRoot82_checked : checkTree [(-5,-3,132),(-1,-1,30),(10,7,-258),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot82 = true := by decide

def target0BackwardRoot83 : CoverTree := .split (1,-1,0) (.leaf 19 [⟨2,[(0,1),(2,7),(3,6)]⟩,⟨2,[(0,1),(2,3),(3,6)]⟩,⟨4,[(0,1),(4,1),(3,12)]⟩,⟨1,[(4,1)]⟩]) (.leaf 20 [⟨1,[(4,1)]⟩,⟨5,[(0,3),(1,2)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨3,[(1,1),(2,1),(3,30)]⟩])
theorem target0BackwardRoot83_checked : checkTree [(-5,-3,132),(5,2,-108),(1,1,-30),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot83 = true := by decide

def target0BackwardRoot84 : CoverTree := .split (-1,1,0) (.leaf 20 [⟨1,[(4,1)]⟩,⟨5,[(0,3),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩]) (.leaf 19 [⟨3,[(1,8),(2,1),(3,24)]⟩,⟨3,[(1,2),(2,1),(3,24)]⟩,⟨5,[(0,3),(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot84_checked : checkTree [(0,-1,24),(1,1,-30),(-5,-2,108),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot84 = true := by decide

def target0BackwardRoot85 : CoverTree := .split (-1,1,0) (.leaf 20 [⟨1,[(4,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,5)]⟩,⟨1,[(0,1),(2,3)]⟩]) (.leaf 19 [⟨5,[(0,4),(1,3)]⟩,⟨5,[(0,1),(1,2),(3,30)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot85_checked : checkTree [(5,4,-126),(-5,-2,108),(-1,-1,30),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot85 = true := by decide

def target0BackwardRoot86 : CoverTree := .split (-1,-2,36) (.split (-1,0,24) (.leaf 17 [⟨2,[(0,1),(4,1),(3,18)]⟩,⟨4,[(0,1),(5,5),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 15 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,3),(1,1)]⟩,⟨5,[(0,17),(1,9)]⟩])) (.leaf 19 [⟨1,[(4,1)]⟩,⟨13,[(1,2),(4,7),(3,48)]⟩,⟨5,[(1,1),(2,1),(3,30)]⟩,⟨15,[(1,7),(2,17),(3,30)]⟩])
theorem target0BackwardRoot86_checked : checkTree [(5,4,-126),(-10,-7,258),(5,2,-108),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot86 = true := by decide

def target0BackwardRoot87 : CoverTree := .leaf 32 [⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨2,[(0,5),(2,3)]⟩]
theorem target0BackwardRoot87_checked : checkTree [(-1,-2,36),(1,1,-6),(1,4,-84),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot87 = true := by decide

theorem targetMeshFamily0Chunk10_covered : FamilyCover targetMeshFamily0Chunk10 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk10,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot80,target0BackwardRoot80_checked⟩
  · exact ⟨target0BackwardRoot81,target0BackwardRoot81_checked⟩
  · exact ⟨target0BackwardRoot82,target0BackwardRoot82_checked⟩
  · exact ⟨target0BackwardRoot83,target0BackwardRoot83_checked⟩
  · exact ⟨target0BackwardRoot84,target0BackwardRoot84_checked⟩
  · exact ⟨target0BackwardRoot85,target0BackwardRoot85_checked⟩
  · exact ⟨target0BackwardRoot86,target0BackwardRoot86_checked⟩
  · exact ⟨target0BackwardRoot87,target0BackwardRoot87_checked⟩

def target0BackwardRoot88 : CoverTree := .leaf 32 [⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨2,[(0,3),(1,1)]⟩,⟨3,[(1,2),(2,1),(3,30)]⟩]
theorem target0BackwardRoot88_checked : checkTree [(1,0,24),(-1,2,-72),(-1,-1,6),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot88 = true := by decide

def target0BackwardRoot89 : CoverTree := .leaf 32 [⟨3,[(1,4),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,2),(1,1),(3,6)]⟩]
theorem target0BackwardRoot89_checked : checkTree [(0,1,-24),(-1,-1,6),(1,-2,72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot89 = true := by decide

def target0BackwardRoot90 : CoverTree := .leaf 32 [⟨1,[(0,2),(1,1)]⟩,⟨3,[(1,1),(2,4),(3,12)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩]
theorem target0BackwardRoot90_checked : checkTree [(0,1,-24),(-1,-4,84),(1,1,-6),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot90 = true := by decide

def target0BackwardRoot91 : CoverTree := .leaf 26 [⟨3,[(1,1),(2,2),(3,30)]⟩,⟨2,[(0,3),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩]
theorem target0BackwardRoot91_checked : checkTree [(0,-1,24),(1,1,6),(-2,1,-72),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot91 = true := by decide

def target0BackwardRoot92 : CoverTree := .leaf 26 [⟨2,[(0,5),(1,3)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target0BackwardRoot92_checked : checkTree [(2,1,36),(-4,-1,-84),(-1,-1,-6),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot92 = true := by decide

def target0BackwardRoot93 : CoverTree := .leaf 26 [⟨1,[(0,5),(2,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨3,[(1,4),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target0BackwardRoot93_checked : checkTree [(-1,0,-24),(-1,-1,-6),(4,1,84),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot93 = true := by decide

def target0BackwardRoot94 : CoverTree := .leaf 26 [⟨1,[(0,2),(2,1),(3,6)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨3,[(1,1),(2,4),(3,12)]⟩]
theorem target0BackwardRoot94_checked : checkTree [(-1,0,-24),(2,-1,72),(1,1,6),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot94 = true := by decide

def target0BackwardRoot95 : CoverTree := .leaf 32 [⟨1,[(0,4),(2,1)]⟩,⟨3,[(1,2),(2,1),(3,12)]⟩,⟨1,[(1,1),(2,1)]⟩,⟨1,[(0,1),(2,1)]⟩]
theorem target0BackwardRoot95_checked : checkTree [(0,-1,24),(2,-1,60),(-1,2,-60),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot95 = true := by decide

theorem targetMeshFamily0Chunk11_covered : FamilyCover targetMeshFamily0Chunk11 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk11,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot88,target0BackwardRoot88_checked⟩
  · exact ⟨target0BackwardRoot89,target0BackwardRoot89_checked⟩
  · exact ⟨target0BackwardRoot90,target0BackwardRoot90_checked⟩
  · exact ⟨target0BackwardRoot91,target0BackwardRoot91_checked⟩
  · exact ⟨target0BackwardRoot92,target0BackwardRoot92_checked⟩
  · exact ⟨target0BackwardRoot93,target0BackwardRoot93_checked⟩
  · exact ⟨target0BackwardRoot94,target0BackwardRoot94_checked⟩
  · exact ⟨target0BackwardRoot95,target0BackwardRoot95_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
