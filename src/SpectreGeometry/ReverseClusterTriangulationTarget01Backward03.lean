module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1BackwardRoot72 : CoverTree := .split (-2,-1,72) (.leaf 63 [⟨1,[(4,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(0,4),(1,1)]⟩,⟨1,[(0,10),(1,3)]⟩]) (.leaf 62 [⟨3,[(1,1),(2,1),(3,48)]⟩,⟨3,[(1,1),(2,7),(3,12)]⟩,⟨1,[(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot72_checked : checkTree [(1,-1,-90),(-3,4,312),(0,-1,-36),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot72 = true := by decide

def target1BackwardRoot73 : CoverTree := .split (0,-1,-36) (.leaf 63 [⟨1,[(0,2),(4,3)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,4),(2,1)]⟩,⟨1,[(0,14),(2,3)]⟩]) (.split (2,1,-72) (.leaf 67 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨3,[(1,4),(2,1),(3,12)]⟩,⟨3,[(1,14),(2,5),(3,24)]⟩]) (.leaf 65 [⟨3,[(1,1),(2,1),(3,48)]⟩,⟨5,[(2,1),(4,9),(3,24)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot73_checked : checkTree [(-1,1,90),(-2,1,144),(5,-4,-408),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot73 = true := by decide

def target1BackwardRoot74 : CoverTree := .leaf 67 [⟨1,[(0,4),(2,3)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(0,4),(1,3)]⟩]
theorem target1BackwardRoot74_checked : checkTree [(-1,1,90),(1,-2,-120),(2,-1,-144),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot74 = true := by decide

def target1BackwardRoot75 : CoverTree := .split (1,2,0) (.leaf 68 [⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,1),(1,1),(3,12)]⟩]) (.leaf 67 [⟨3,[(1,5),(2,4),(3,24)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot75_checked : checkTree [(-1,0,60),(2,-1,-144),(-1,2,120),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot75 = true := by decide

def target1BackwardRoot76 : CoverTree := .split (-1,-2,0) (.leaf 67 [⟨4,[(0,5),(1,7),(3,12)]⟩,⟨4,[(0,1),(1,3),(3,12)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨1,[(4,1)]⟩]) (.leaf 68 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,3),(2,5)]⟩,⟨1,[(0,1),(2,1),(3,12)]⟩])
theorem target1BackwardRoot76_checked : checkTree [(3,-2,-228),(-1,2,120),(-2,1,144),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot76 = true := by decide

def target1BackwardRoot77 : CoverTree := .split (-2,-1,72) (.split (0,-1,-36) (.leaf 63 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨1,[(0,7),(1,4)]⟩]) (.leaf 65 [⟨1,[(2,1),(5,1),(3,12)]⟩,⟨1,[(2,1),(5,3)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.leaf 67 [⟨1,[(4,1)]⟩,⟨13,[(1,2),(4,5),(3,12)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩,⟨3,[(1,2),(2,7),(3,24)]⟩])
theorem target1BackwardRoot77_checked : checkTree [(3,-2,-228),(-5,4,408),(1,-2,-120),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot77 = true := by decide

def target1BackwardRoot78 : CoverTree := .split (-2,-1,72) (.split (0,-1,-36) (.leaf 63 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,3),(2,2)]⟩,⟨5,[(0,17),(2,8)]⟩]) (.leaf 65 [⟨3,[(1,4),(2,1),(3,30)]⟩,⟨7,[(2,1),(5,10),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.leaf 67 [⟨1,[(4,1)]⟩,⟨1,[(1,2),(4,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨3,[(1,17),(2,2),(3,6)]⟩])
theorem target1BackwardRoot78_checked : checkTree [(-3,2,228),(-1,0,54),(7,-3,-462),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot78 = true := by decide

def target1BackwardRoot79 : CoverTree := .split (-1,-2,0) (.leaf 67 [⟨2,[(0,1),(2,7),(3,6)]⟩,⟨2,[(0,1),(2,3),(3,6)]⟩,⟨4,[(0,1),(4,1),(3,12)]⟩,⟨1,[(4,1)]⟩]) (.leaf 68 [⟨1,[(4,1)]⟩,⟨5,[(0,3),(1,2)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨3,[(1,1),(2,1),(3,30)]⟩])
theorem target1BackwardRoot79_checked : checkTree [(-3,2,228),(2,-3,-192),(1,0,-54),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot79 = true := by decide

theorem targetMeshFamily1Chunk9_covered : FamilyCover targetMeshFamily1Chunk9 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk9,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot72,target1BackwardRoot72_checked⟩
  · exact ⟨target1BackwardRoot73,target1BackwardRoot73_checked⟩
  · exact ⟨target1BackwardRoot74,target1BackwardRoot74_checked⟩
  · exact ⟨target1BackwardRoot75,target1BackwardRoot75_checked⟩
  · exact ⟨target1BackwardRoot76,target1BackwardRoot76_checked⟩
  · exact ⟨target1BackwardRoot77,target1BackwardRoot77_checked⟩
  · exact ⟨target1BackwardRoot78,target1BackwardRoot78_checked⟩
  · exact ⟨target1BackwardRoot79,target1BackwardRoot79_checked⟩

def target1BackwardRoot80 : CoverTree := .split (1,2,0) (.leaf 68 [⟨1,[(4,1)]⟩,⟨5,[(0,3),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩]) (.leaf 67 [⟨3,[(1,8),(2,1),(3,24)]⟩,⟨3,[(1,2),(2,1),(3,24)]⟩,⟨5,[(0,3),(2,1)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot80_checked : checkTree [(-1,-1,36),(1,0,-54),(-2,3,192),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot80 = true := by decide

def target1BackwardRoot81 : CoverTree := .split (1,2,0) (.leaf 68 [⟨1,[(4,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,5)]⟩,⟨1,[(0,1),(2,3)]⟩]) (.leaf 67 [⟨5,[(0,4),(1,3)]⟩,⟨5,[(0,1),(1,2),(3,30)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot81_checked : checkTree [(4,-1,-234),(-2,3,192),(-1,0,54),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot81 = true := by decide

def target1BackwardRoot82 : CoverTree := .split (-2,-1,72) (.split (0,1,36) (.leaf 65 [⟨2,[(0,1),(4,1),(3,18)]⟩,⟨4,[(0,1),(5,5),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 63 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,3),(1,1)]⟩,⟨5,[(0,17),(1,9)]⟩])) (.leaf 67 [⟨1,[(4,1)]⟩,⟨13,[(1,2),(4,7),(3,48)]⟩,⟨5,[(1,1),(2,1),(3,30)]⟩,⟨15,[(1,7),(2,17),(3,30)]⟩])
theorem target1BackwardRoot82_checked : checkTree [(4,-1,-234),(-7,3,462),(2,-3,-192),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot82 = true := by decide

def target1BackwardRoot83 : CoverTree := .leaf 14 [⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨2,[(0,5),(2,3)]⟩]
theorem target1BackwardRoot83_checked : checkTree [(-2,-1,72),(1,0,-30),(4,3,-144),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot83 = true := by decide

def target1BackwardRoot84 : CoverTree := .leaf 14 [⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨2,[(0,3),(1,1)]⟩,⟨3,[(1,2),(2,1),(3,30)]⟩]
theorem target1BackwardRoot84_checked : checkTree [(0,-1,12),(2,3,-84),(-1,0,30),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot84 = true := by decide

def target1BackwardRoot85 : CoverTree := .leaf 14 [⟨3,[(1,4),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,2),(1,1),(3,6)]⟩]
theorem target1BackwardRoot85_checked : checkTree [(1,1,-36),(-1,0,30),(-2,-3,84),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot85 = true := by decide

def target1BackwardRoot86 : CoverTree := .leaf 14 [⟨1,[(0,2),(1,1)]⟩,⟨3,[(1,1),(2,4),(3,12)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩]
theorem target1BackwardRoot86_checked : checkTree [(1,1,-36),(-4,-3,144),(1,0,-30),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot86 = true := by decide

def target1BackwardRoot87 : CoverTree := .leaf 32 [⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨2,[(0,5),(2,3)]⟩]
theorem target1BackwardRoot87_checked : checkTree [(-1,-2,36),(1,1,-6),(1,4,-84),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot87 = true := by decide

theorem targetMeshFamily1Chunk10_covered : FamilyCover targetMeshFamily1Chunk10 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk10,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot80,target1BackwardRoot80_checked⟩
  · exact ⟨target1BackwardRoot81,target1BackwardRoot81_checked⟩
  · exact ⟨target1BackwardRoot82,target1BackwardRoot82_checked⟩
  · exact ⟨target1BackwardRoot83,target1BackwardRoot83_checked⟩
  · exact ⟨target1BackwardRoot84,target1BackwardRoot84_checked⟩
  · exact ⟨target1BackwardRoot85,target1BackwardRoot85_checked⟩
  · exact ⟨target1BackwardRoot86,target1BackwardRoot86_checked⟩
  · exact ⟨target1BackwardRoot87,target1BackwardRoot87_checked⟩

def target1BackwardRoot88 : CoverTree := .leaf 32 [⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨2,[(0,3),(1,1)]⟩,⟨3,[(1,2),(2,1),(3,30)]⟩]
theorem target1BackwardRoot88_checked : checkTree [(1,0,24),(-1,2,-72),(-1,-1,6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot88 = true := by decide

def target1BackwardRoot89 : CoverTree := .leaf 32 [⟨3,[(1,4),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(0,3),(2,1)]⟩,⟨1,[(0,2),(1,1),(3,6)]⟩]
theorem target1BackwardRoot89_checked : checkTree [(0,1,-24),(-1,-1,6),(1,-2,72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot89 = true := by decide

def target1BackwardRoot90 : CoverTree := .leaf 32 [⟨1,[(0,2),(1,1)]⟩,⟨3,[(1,1),(2,4),(3,12)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,5),(1,1)]⟩]
theorem target1BackwardRoot90_checked : checkTree [(0,1,-24),(-1,-4,84),(1,1,-6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot90 = true := by decide

def target1BackwardRoot91 : CoverTree := .leaf 26 [⟨3,[(1,1),(2,2),(3,30)]⟩,⟨2,[(0,3),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,2)]⟩]
theorem target1BackwardRoot91_checked : checkTree [(0,-1,24),(1,1,6),(-2,1,-72),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot91 = true := by decide

def target1BackwardRoot92 : CoverTree := .leaf 26 [⟨2,[(0,5),(1,3)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target1BackwardRoot92_checked : checkTree [(2,1,36),(-4,-1,-84),(-1,-1,-6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot92 = true := by decide

def target1BackwardRoot93 : CoverTree := .leaf 26 [⟨1,[(0,5),(2,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨3,[(1,4),(2,1),(3,12)]⟩,⟨1,[(0,2),(2,1)]⟩]
theorem target1BackwardRoot93_checked : checkTree [(-1,0,-24),(-1,-1,-6),(4,1,84),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot93 = true := by decide

def target1BackwardRoot94 : CoverTree := .leaf 26 [⟨1,[(0,2),(2,1),(3,6)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,2),(1,1)]⟩,⟨3,[(1,1),(2,4),(3,12)]⟩]
theorem target1BackwardRoot94_checked : checkTree [(-1,0,-24),(2,-1,72),(1,1,6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot94 = true := by decide

def target1BackwardRoot95 : CoverTree := .leaf 32 [⟨1,[(0,4),(2,1)]⟩,⟨3,[(1,2),(2,1),(3,12)]⟩,⟨1,[(1,1),(2,1)]⟩,⟨1,[(0,1),(2,1)]⟩]
theorem target1BackwardRoot95_checked : checkTree [(0,-1,24),(2,-1,60),(-1,2,-60),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot95 = true := by decide

theorem targetMeshFamily1Chunk11_covered : FamilyCover targetMeshFamily1Chunk11 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk11,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot88,target1BackwardRoot88_checked⟩
  · exact ⟨target1BackwardRoot89,target1BackwardRoot89_checked⟩
  · exact ⟨target1BackwardRoot90,target1BackwardRoot90_checked⟩
  · exact ⟨target1BackwardRoot91,target1BackwardRoot91_checked⟩
  · exact ⟨target1BackwardRoot92,target1BackwardRoot92_checked⟩
  · exact ⟨target1BackwardRoot93,target1BackwardRoot93_checked⟩
  · exact ⟨target1BackwardRoot94,target1BackwardRoot94_checked⟩
  · exact ⟨target1BackwardRoot95,target1BackwardRoot95_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
