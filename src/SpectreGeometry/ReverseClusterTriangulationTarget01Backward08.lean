module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1BackwardRoot192 : CoverTree := .split (1,0,-48) (.leaf 71 [⟨1,[(0,2),(4,3)]⟩,⟨1,[(4,1)]⟩,⟨3,[(0,1),(2,1)]⟩,⟨1,[(0,3),(2,1)]⟩]) (.leaf 73 [⟨3,[(1,1),(2,2),(3,36)]⟩,⟨4,[(2,1),(4,5),(3,6)]⟩,⟨1,[(4,1)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩])
theorem target1BackwardRoot192_checked : checkTree [(-2,-1,90),(-4,-5,144),(5,4,-198),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot192 = true := by decide

def target1BackwardRoot193 : CoverTree := .split (1,0,-48) (.leaf 71 [⟨1,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩,⟨5,[(2,1),(4,1),(3,12)]⟩,⟨2,[(0,3),(2,1),(3,18)]⟩]) (.leaf 73 [⟨3,[(1,2),(2,1),(3,36)]⟩,⟨3,[(0,2),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1),(1,1)]⟩])
theorem target1BackwardRoot193_checked : checkTree [(-2,-1,90),(1,-1,-54),(4,5,-144),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot193 = true := by decide

def target1BackwardRoot194 : CoverTree := .leaf 73 [⟨1,[(0,2),(1,1)]⟩,⟨9,[(1,1),(2,4),(3,36)]⟩,⟨3,[(0,1),(2,2)]⟩,⟨1,[(0,1)]⟩]
theorem target1BackwardRoot194_checked : checkTree [(-1,-2,36),(4,5,-144),(-1,1,54),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot194 = true := by decide

def target1BackwardRoot195 : CoverTree := .leaf 73 [⟨1,[(0,6),(2,1)]⟩,⟨2,[(0,1),(1,1),(3,6)]⟩,⟨9,[(1,5),(2,1),(3,18)]⟩,⟨1,[(0,3),(2,1)]⟩]
theorem target1BackwardRoot195_checked : checkTree [(1,1,-36),(-1,1,54),(-4,-5,144),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot195 = true := by decide

def target1BackwardRoot196 : CoverTree := .split (1,0,-48) (.leaf 71 [⟨2,[(1,1),(4,3),(3,18)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,9),(1,2)]⟩]) (.leaf 73 [⟨2,[(0,3),(2,1),(3,18)]⟩,⟨1,[(0,1),(4,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(2,2),(4,3)]⟩])
theorem target1BackwardRoot196_checked : checkTree [(1,1,-36),(-5,-4,198),(1,-1,-54),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot196 = true := by decide

def target1BackwardRoot197 : CoverTree := .split (-1,0,24) (.split (1,-1,0) (.leaf 19 [⟨1,[(1,1)]⟩,⟨1,[(4,1)]⟩,⟨9,[(1,2),(2,1),(3,18)]⟩,⟨1,[(5,1)]⟩]) (.leaf 20 [⟨1,[(5,1)]⟩,⟨9,[(1,2),(2,1),(3,18)]⟩,⟨3,[(0,11),(2,7)]⟩,⟨1,[(0,5),(2,3)]⟩])) (.leaf 14 [⟨3,[(1,5),(2,1),(3,18)]⟩,⟨13,[(2,1),(4,11),(3,42)]⟩,⟨1,[(4,1)]⟩,⟨1,[(1,1)]⟩])
theorem target1BackwardRoot197_checked : checkTree [(7,8,-234),(1,2,-36),(-11,-13,378),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot197 = true := by decide

def target1BackwardRoot198 : CoverTree := .split (2,1,-72) (.split (0,1,12) (.leaf 73 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨10,[(1,1),(5,11),(3,6)]⟩,⟨1,[(2,1)]⟩]) (.leaf 69 [⟨1,[(0,7),(1,5)]⟩,⟨3,[(0,1),(1,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.split (-1,1,36) (.leaf 15 [⟨1,[(2,1)]⟩,⟨3,[(0,1),(2,4),(3,18)]⟩,⟨6,[(0,1),(2,1),(3,54)]⟩,⟨1,[(5,1)]⟩]) (.leaf 72 [⟨1,[(5,1)]⟩,⟨6,[(0,1),(2,1),(3,54)]⟩,⟨9,[(0,2),(4,7),(3,72)]⟩,⟨1,[(4,1)]⟩]))
theorem target1BackwardRoot198_checked : checkTree [(7,8,-234),(-10,-11,342),(-1,-2,36),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot198 = true := by decide

def target1BackwardRoot199 : CoverTree := .split (0,1,12) (.split (2,1,-72) (.leaf 73 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1),(4,1)]⟩,⟨1,[(0,3),(5,1)]⟩]) (.split (1,-1,-36) (.leaf 72 [⟨1,[(6,1)]⟩,⟨9,[(1,1),(2,2),(3,90)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 15 [⟨1,[(1,1),(2,1)]⟩,⟨9,[(1,11),(2,13),(3,72)]⟩,⟨9,[(1,1),(2,2),(3,90)]⟩,⟨1,[(6,1)]⟩]))) (.leaf 69 [⟨1,[(0,21),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩,⟨5,[(2,1),(4,6),(3,54)]⟩])
theorem target1BackwardRoot199_checked : checkTree [(-1,-1,36),(-11,-13,378),(10,11,-342),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot199 = true := by decide

theorem targetMeshFamily1Chunk24_covered : FamilyCover targetMeshFamily1Chunk24 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk24,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot192,target1BackwardRoot192_checked⟩
  · exact ⟨target1BackwardRoot193,target1BackwardRoot193_checked⟩
  · exact ⟨target1BackwardRoot194,target1BackwardRoot194_checked⟩
  · exact ⟨target1BackwardRoot195,target1BackwardRoot195_checked⟩
  · exact ⟨target1BackwardRoot196,target1BackwardRoot196_checked⟩
  · exact ⟨target1BackwardRoot197,target1BackwardRoot197_checked⟩
  · exact ⟨target1BackwardRoot198,target1BackwardRoot198_checked⟩
  · exact ⟨target1BackwardRoot199,target1BackwardRoot199_checked⟩

def target1BackwardRoot200 : CoverTree := .split (2,1,-72) (.leaf 73 [⟨1,[(4,1)]⟩,⟨2,[(0,11),(2,1),(3,6)]⟩,⟨2,[(0,13),(2,1),(3,6)]⟩,⟨1,[(1,1)]⟩]) (.split (-1,1,36) (.leaf 15 [⟨1,[(1,1)]⟩,⟨9,[(1,13),(2,2),(3,72)]⟩,⟨9,[(1,2),(2,1),(3,90)]⟩,⟨1,[(5,1)]⟩]) (.leaf 72 [⟨1,[(5,1)]⟩,⟨9,[(1,2),(2,1),(3,90)]⟩,⟨2,[(0,11),(2,1),(3,6)]⟩,⟨1,[(4,1)]⟩]))
theorem target1BackwardRoot200_checked : checkTree [(-1,-1,36),(-1,-2,36),(11,13,-378),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot200 = true := by decide

def target1BackwardRoot201 : CoverTree := .split (1,0,-24) (.leaf 14 [⟨1,[(0,1),(2,2)]⟩,⟨3,[(0,5),(1,2)]⟩,⟨1,[(4,1)]⟩,⟨1,[(2,1)]⟩]) (.leaf 19 [⟨1,[(2,1)]⟩,⟨1,[(4,1)]⟩,⟨3,[(0,1),(2,1)]⟩,⟨2,[(0,7),(1,3),(3,18)]⟩])
theorem target1BackwardRoot201_checked : checkTree [(-4,-5,144),(10,11,-342),(1,2,-36),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot201 = true := by decide

def target1BackwardRoot202 : CoverTree := .split (1,-1,0) (.split (-1,0,24) (.leaf 19 [⟨1,[(1,1),(2,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,1),(5,1),(3,12)]⟩,⟨1,[(4,1)]⟩]) (.leaf 14 [⟨3,[(1,4),(2,5),(3,18)]⟩,⟨5,[(0,1),(5,4),(3,12)]⟩,⟨1,[(5,1)]⟩,⟨1,[(1,1),(2,1)]⟩])) (.leaf 20 [⟨1,[(4,1)]⟩,⟨9,[(0,2),(4,1),(3,36)]⟩,⟨3,[(0,11),(1,4)]⟩,⟨1,[(0,5),(1,2)]⟩])
theorem target1BackwardRoot202_checked : checkTree [(-4,-5,144),(11,13,-378),(-10,-11,342),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot202 = true := by decide

def target1BackwardRoot203 : CoverTree := .split (1,-1,0) (.leaf 19 [⟨1,[(1,3),(4,1)]⟩,⟨3,[(1,4),(2,1),(3,6)]⟩,⟨3,[(1,1),(2,1),(3,6)]⟩,⟨1,[(4,1)]⟩]) (.leaf 20 [⟨1,[(4,1)]⟩,⟨3,[(1,1),(2,1),(3,6)]⟩,⟨1,[(0,3),(2,4)]⟩,⟨1,[(0,5),(2,6)]⟩])
theorem target1BackwardRoot203_checked : checkTree [(4,5,-144),(0,1,-12),(-3,-4,114),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot203 = true := by decide

def target1BackwardRoot204 : CoverTree := .split (1,0,-24) (.leaf 14 [⟨1,[(0,4),(1,3)]⟩,⟨1,[(2,1)]⟩,⟨1,[(4,1)]⟩,⟨2,[(0,5),(1,3)]⟩]) (.leaf 19 [⟨2,[(0,5),(1,3)]⟩,⟨1,[(4,1)]⟩,⟨1,[(2,1),(4,1)]⟩,⟨4,[(0,1),(2,9),(3,36)]⟩])
theorem target1BackwardRoot204_checked : checkTree [(4,5,-144),(-6,-7,216),(0,-1,12),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot204 = true := by decide

def target1BackwardRoot205 : CoverTree := .split (1,0,-24) (.leaf 14 [⟨1,[(0,8),(2,1)]⟩,⟨1,[(0,1),(4,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,5),(2,1)]⟩]) (.leaf 19 [⟨1,[(0,5),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨3,[(1,13),(2,7),(3,30)]⟩])
theorem target1BackwardRoot205_checked : checkTree [(-1,-1,36),(-3,-4,114),(6,7,-216),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot205 = true := by decide

def target1BackwardRoot206 : CoverTree := .split (1,0,-24) (.leaf 14 [⟨1,[(0,5),(2,1),(3,6)]⟩,⟨1,[(1,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,2),(2,1),(3,6)]⟩]) (.leaf 19 [⟨1,[(0,2),(2,1),(3,6)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨3,[(1,7),(2,1),(3,30)]⟩])
theorem target1BackwardRoot206_checked : checkTree [(-1,-1,36),(0,-1,12),(3,4,-114),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot206 = true := by decide

def target1BackwardRoot207 : CoverTree := .split (1,-1,0) (.leaf 19 [⟨1,[(2,3),(4,1)]⟩,⟨2,[(0,1),(2,3)]⟩,⟨2,[(0,1),(2,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 20 [⟨1,[(4,1)]⟩,⟨2,[(0,1),(2,1)]⟩,⟨2,[(0,3),(1,1),(3,12)]⟩,⟨1,[(0,2),(1,1),(3,12)]⟩])
theorem target1BackwardRoot207_checked : checkTree [(-2,-3,84),(6,7,-216),(0,1,-12),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot207 = true := by decide

theorem targetMeshFamily1Chunk25_covered : FamilyCover targetMeshFamily1Chunk25 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk25,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot200,target1BackwardRoot200_checked⟩
  · exact ⟨target1BackwardRoot201,target1BackwardRoot201_checked⟩
  · exact ⟨target1BackwardRoot202,target1BackwardRoot202_checked⟩
  · exact ⟨target1BackwardRoot203,target1BackwardRoot203_checked⟩
  · exact ⟨target1BackwardRoot204,target1BackwardRoot204_checked⟩
  · exact ⟨target1BackwardRoot205,target1BackwardRoot205_checked⟩
  · exact ⟨target1BackwardRoot206,target1BackwardRoot206_checked⟩
  · exact ⟨target1BackwardRoot207,target1BackwardRoot207_checked⟩

def target1BackwardRoot208 : CoverTree := .split (-1,1,0) (.leaf 20 [⟨1,[(4,1)]⟩,⟨3,[(1,1),(2,1),(3,6)]⟩,⟨1,[(0,3),(1,2)]⟩,⟨1,[(0,5),(1,4)]⟩]) (.leaf 19 [⟨3,[(1,5),(2,2),(3,30)]⟩,⟨3,[(1,7),(2,4),(3,6)]⟩,⟨3,[(1,1),(2,1),(3,6)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot208_checked : checkTree [(-2,-3,84),(3,4,-114),(-6,-7,216),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot208 = true := by decide

def target1BackwardRoot209 : CoverTree := .leaf 20 [⟨3,[(1,8),(2,1),(3,6)]⟩,⟨3,[(1,2),(2,1),(3,6)]⟩,⟨1,[(0,3),(2,2)]⟩,⟨1,[(0,7),(2,4)]⟩]
theorem target1BackwardRoot209_checked : checkTree [(2,3,-84),(0,1,-18),(-3,-5,138),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot209 = true := by decide

def target1BackwardRoot210 : CoverTree := .split (1,-1,0) (.leaf 19 [⟨1,[(0,2),(1,1),(3,12)]⟩,⟨1,[(0,4),(1,3)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 20 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,2),(3,12)]⟩])
theorem target1BackwardRoot210_checked : checkTree [(2,3,-84),(-3,-4,120),(0,-1,18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot210 = true := by decide

def target1BackwardRoot211 : CoverTree := .split (1,-1,0) (.leaf 19 [⟨1,[(0,2),(2,1),(3,12)]⟩,⟨1,[(0,4),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 20 [⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨3,[(1,5),(2,2),(3,42)]⟩])
theorem target1BackwardRoot211_checked : checkTree [(-1,-1,36),(0,-1,18),(3,4,-120),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot211 = true := by decide

def target1BackwardRoot212 : CoverTree := .leaf 20 [⟨1,[(0,1),(2,3)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨2,[(0,3),(1,1),(3,6)]⟩,⟨2,[(0,5),(1,3),(3,18)]⟩]
theorem target1BackwardRoot212_checked : checkTree [(-1,-2,54),(3,4,-120),(0,1,-18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot212 = true := by decide

def target1BackwardRoot213 : CoverTree := .leaf 20 [⟨3,[(1,7),(2,8),(3,6)]⟩,⟨3,[(1,1),(2,2),(3,6)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,7),(1,3)]⟩]
theorem target1BackwardRoot213_checked : checkTree [(-1,-2,54),(3,5,-138),(-3,-4,120),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot213 = true := by decide

def target1BackwardRoot214 : CoverTree := .leaf 20 [⟨1,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨3,[(1,4),(2,1),(3,30)]⟩]
theorem target1BackwardRoot214_checked : checkTree [(-1,-1,36),(1,0,-12),(2,3,-90),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot214 = true := by decide

def target1BackwardRoot215 : CoverTree := .leaf 20 [⟨3,[(1,1),(2,4),(3,30)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,5),(1,2)]⟩]
theorem target1BackwardRoot215_checked : checkTree [(0,-1,24),(1,3,-78),(-1,0,12),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot215 = true := by decide

theorem targetMeshFamily1Chunk26_covered : FamilyCover targetMeshFamily1Chunk26 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk26,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot208,target1BackwardRoot208_checked⟩
  · exact ⟨target1BackwardRoot209,target1BackwardRoot209_checked⟩
  · exact ⟨target1BackwardRoot210,target1BackwardRoot210_checked⟩
  · exact ⟨target1BackwardRoot211,target1BackwardRoot211_checked⟩
  · exact ⟨target1BackwardRoot212,target1BackwardRoot212_checked⟩
  · exact ⟨target1BackwardRoot213,target1BackwardRoot213_checked⟩
  · exact ⟨target1BackwardRoot214,target1BackwardRoot214_checked⟩
  · exact ⟨target1BackwardRoot215,target1BackwardRoot215_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
