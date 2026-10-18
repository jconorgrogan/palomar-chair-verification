module

public import SpectreGeometry.ReverseClusterTriangulationTarget00Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target0BackwardRoot168 : CoverTree := .split (0,1,24) (.split (-1,-2,0) (.leaf 11 [⟨3,[(0,2),(1,1)]⟩,⟨1,[(4,1)]⟩,⟨4,[(0,1),(4,3),(3,6)]⟩,⟨1,[(5,1)]⟩]) (.split (-1,1,36) (.leaf 13 [⟨1,[(6,1)]⟩,⟨6,[(0,5),(1,1),(3,54)]⟩,⟨3,[(0,7),(1,2),(3,18)]⟩,⟨3,[(0,2),(1,1)]⟩]) (.leaf 12 [⟨1,[(5,1)]⟩,⟨4,[(0,1),(4,3),(3,6)]⟩,⟨6,[(0,5),(1,1),(3,54)]⟩,⟨1,[(6,1)]⟩]))) (.split (-1,1,72) (.leaf 58 [⟨1,[(5,1)]⟩,⟨4,[(0,1),(4,1),(3,6)]⟩,⟨1,[(4,1)]⟩,⟨3,[(0,2),(1,1)]⟩]) (.leaf 61 [⟨3,[(0,13),(2,5)]⟩,⟨1,[(0,3),(2,1)]⟩,⟨4,[(0,1),(4,1),(3,6)]⟩,⟨1,[(5,1)]⟩]))
theorem target0BackwardRoot168_checked : checkTree [(-4,-3,66),(14,9,-240),(11,9,-150),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot168 = true := by decide

def target0BackwardRoot169 : CoverTree := .split (0,1,0) (.split (-1,1,0) (.split (1,2,-36) (.split (1,0,0) (.leaf 21 [⟨2,[(0,1),(4,1),(3,6)]⟩,⟨3,[(0,1),(7,4),(3,6)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 25 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨3,[(0,7),(1,1)]⟩,⟨3,[(0,43),(1,7)]⟩])) (.leaf 18 [⟨1,[(6,1)]⟩,⟨16,[(1,1),(6,9),(3,66)]⟩,⟨25,[(1,1),(4,7),(3,90)]⟩,⟨1,[(5,1)]⟩])) (.leaf 16 [⟨1,[(5,1)]⟩,⟨25,[(1,1),(4,7),(3,90)]⟩,⟨1,[(4,1)]⟩,⟨2,[(0,1),(4,1),(3,6)]⟩])) (.split (-2,-1,36) (.leaf 10 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨25,[(1,1),(4,18),(3,90)]⟩,⟨11,[(1,3),(5,32),(3,18)]⟩]) (.split (1,-1,-36) (.split (-1,-2,0) (.leaf 11 [⟨1,[(5,1)]⟩,⟨27,[(1,14),(2,25),(3,108)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨1,[(7,1)]⟩]) (.leaf 12 [⟨1,[(7,1)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨2,[(0,1),(5,1),(3,18)]⟩,⟨1,[(6,1)]⟩])) (.leaf 13 [⟨1,[(6,1)]⟩,⟨2,[(0,1),(5,1),(3,18)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩])))
theorem target0BackwardRoot169_checked : checkTree [(-4,-3,66),(25,18,-390),(-14,-9,240),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot169 = true := by decide

def target0BackwardRoot170 : CoverTree := .leaf 63 [⟨3,[(1,8),(2,1),(3,6)]⟩,⟨3,[(1,2),(2,1),(3,6)]⟩,⟨1,[(0,3),(2,2)]⟩,⟨1,[(0,7),(2,4)]⟩]
theorem target0BackwardRoot170_checked : checkTree [(-1,2,132),(-1,0,54),(2,-3,-222),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot170 = true := by decide

def target0BackwardRoot171 : CoverTree := .split (2,1,-72) (.leaf 62 [⟨1,[(0,2),(1,1),(3,12)]⟩,⟨1,[(0,4),(1,3)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 63 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,2),(3,12)]⟩])
theorem target0BackwardRoot171_checked : checkTree [(-1,2,132),(1,-3,-168),(1,0,-54),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot171 = true := by decide

def target0BackwardRoot172 : CoverTree := .split (2,1,-72) (.leaf 62 [⟨1,[(0,2),(2,1),(3,12)]⟩,⟨1,[(0,4),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 63 [⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨3,[(1,5),(2,2),(3,42)]⟩])
theorem target0BackwardRoot172_checked : checkTree [(0,-1,-36),(1,0,-54),(-1,3,168),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot172 = true := by decide

def target0BackwardRoot173 : CoverTree := .leaf 63 [⟨1,[(0,1),(2,3)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨2,[(0,3),(1,1),(3,6)]⟩,⟨2,[(0,5),(1,3),(3,18)]⟩]
theorem target0BackwardRoot173_checked : checkTree [(1,-1,-90),(-1,3,168),(-1,0,54),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot173 = true := by decide

def target0BackwardRoot174 : CoverTree := .leaf 63 [⟨3,[(1,7),(2,8),(3,6)]⟩,⟨3,[(1,1),(2,2),(3,6)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,7),(1,3)]⟩]
theorem target0BackwardRoot174_checked : checkTree [(1,-1,-90),(-2,3,222),(1,-3,-168),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot174 = true := by decide

def target0BackwardRoot175 : CoverTree := .split (1,0,-48) (.split (0,-1,-36) (.leaf 63 [⟨1,[(0,2),(5,3)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,2),(4,3)]⟩]) (.leaf 65 [⟨3,[(1,1),(2,2),(3,18)]⟩,⟨1,[(4,1),(5,1)]⟩,⟨1,[(5,1)]⟩,⟨4,[(0,1),(1,1),(3,36)]⟩])) (.split (-1,-1,12) (.leaf 61 [⟨1,[(2,2),(4,9)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨2,[(2,1),(5,3),(3,18)]⟩]) (.leaf 65 [⟨3,[(1,1),(2,2),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1),(5,1)]⟩,⟨2,[(1,1),(5,3),(3,18)]⟩]))
theorem target0BackwardRoot175_checked : checkTree [(-1,1,90),(-7,-5,162),(5,1,-198),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot175 = true := by decide

theorem targetMeshFamily0Chunk21_covered : FamilyCover targetMeshFamily0Chunk21 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk21,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot168,target0BackwardRoot168_checked⟩
  · exact ⟨target0BackwardRoot169,target0BackwardRoot169_checked⟩
  · exact ⟨target0BackwardRoot170,target0BackwardRoot170_checked⟩
  · exact ⟨target0BackwardRoot171,target0BackwardRoot171_checked⟩
  · exact ⟨target0BackwardRoot172,target0BackwardRoot172_checked⟩
  · exact ⟨target0BackwardRoot173,target0BackwardRoot173_checked⟩
  · exact ⟨target0BackwardRoot174,target0BackwardRoot174_checked⟩
  · exact ⟨target0BackwardRoot175,target0BackwardRoot175_checked⟩

def target0BackwardRoot176 : CoverTree := .split (0,1,36) (.leaf 65 [⟨3,[(1,4),(2,1),(3,18)]⟩,⟨6,[(0,1),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1),(1,1)]⟩]) (.leaf 63 [⟨1,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩,⟨7,[(2,1),(4,5),(3,6)]⟩,⟨4,[(0,3),(2,1),(3,36)]⟩])
theorem target0BackwardRoot176_checked : checkTree [(-1,1,90),(-1,-2,-18),(7,5,-162),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot176 = true := by decide

def target0BackwardRoot177 : CoverTree := .leaf 65 [⟨2,[(0,3),(1,1)]⟩,⟨9,[(1,1),(2,4),(3,18)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨1,[(0,3),(2,1)]⟩]
theorem target0BackwardRoot177_checked : checkTree [(-1,-1,18),(5,1,-198),(1,2,18),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot177 = true := by decide

def target0BackwardRoot178 : CoverTree := .split (-1,1,72) (.leaf 64 [⟨2,[(0,9),(1,1)]⟩,⟨2,[(0,5),(1,1)]⟩,⟨6,[(1,1),(4,1),(3,18)]⟩,⟨1,[(4,1)]⟩]) (.leaf 65 [⟨1,[(4,1)]⟩,⟨9,[(1,2),(2,1),(3,18)]⟩,⟨18,[(1,5),(2,7),(3,72)]⟩,⟨2,[(2,1),(4,1),(3,18)]⟩])
theorem target0BackwardRoot178_checked : checkTree [(-1,-1,18),(7,5,-162),(-5,-1,198),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot178 = true := by decide

def target0BackwardRoot179 : CoverTree := .split (-1,1,72) (.leaf 64 [⟨1,[(0,3),(2,1)]⟩,⟨3,[(0,5),(2,1)]⟩,⟨3,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 65 [⟨1,[(4,1)]⟩,⟨3,[(0,1),(1,1)]⟩,⟨9,[(1,7),(2,1),(3,36)]⟩,⟨3,[(1,1),(2,1),(3,36)]⟩])
theorem target0BackwardRoot179_checked : checkTree [(2,1,-54),(1,2,18),(-7,-5,162),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot179 = true := by decide

def target0BackwardRoot180 : CoverTree := .split (-1,-1,12) (.leaf 61 [⟨1,[(0,3),(1,1)]⟩,⟨3,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1),(2,1)]⟩]) (.leaf 65 [⟨1,[(0,1),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨4,[(1,1),(4,5),(3,6)]⟩,⟨3,[(1,1),(2,1),(3,36)]⟩])
theorem target0BackwardRoot180_checked : checkTree [(2,1,-54),(-5,-1,198),(-1,-2,-18),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot180 = true := by decide

def target0BackwardRoot181 : CoverTree := .split (0,1,0) (.split (-1,1,0) (.split (1,2,-36) (.split (1,0,0) (.leaf 21 [⟨2,[(2,1),(6,1),(3,18)]⟩,⟨4,[(2,1),(7,5),(3,6)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 25 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨1,[(0,9),(2,7)]⟩])) (.leaf 18 [⟨1,[(6,1)]⟩,⟨5,[(0,2),(6,3),(3,24)]⟩,⟨4,[(0,1),(4,1),(3,18)]⟩,⟨1,[(5,1)]⟩])) (.leaf 16 [⟨1,[(5,1)]⟩,⟨4,[(0,1),(4,1),(3,18)]⟩,⟨1,[(4,1)]⟩,⟨5,[(2,2),(4,3)]⟩])) (.split (2,1,-36) (.leaf 13 [⟨1,[(1,1),(2,1)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 10 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨4,[(0,1),(4,3),(3,18)]⟩,⟨2,[(0,3),(5,5),(3,18)]⟩]))
theorem target0BackwardRoot181_checked : checkTree [(4,3,-66),(4,5,-54),(-5,-4,90),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot181 = true := by decide

def target0BackwardRoot182 : CoverTree := .split (-1,-2,0) (.split (0,1,24) (.leaf 11 [⟨4,[(0,3),(2,1)]⟩,⟨1,[(5,1)]⟩,⟨16,[(1,1),(5,11),(3,6)]⟩,⟨1,[(4,1)]⟩]) (.split (-1,1,72) (.leaf 58 [⟨1,[(6,1)]⟩,⟨16,[(1,1),(5,5),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨2,[(0,1),(5,1),(3,18)]⟩]) (.leaf 61 [⟨4,[(0,21),(1,5)]⟩,⟨4,[(0,11),(1,3)]⟩,⟨16,[(1,1),(5,5),(3,6)]⟩,⟨1,[(6,1)]⟩]))) (.split (1,-1,-36) (.leaf 12 [⟨1,[(4,1)]⟩,⟨3,[(2,2),(4,5)]⟩,⟨3,[(2,1),(4,1),(3,18)]⟩,⟨1,[(5,1)]⟩]) (.leaf 13 [⟨1,[(5,1)]⟩,⟨3,[(2,1),(4,1),(3,18)]⟩,⟨2,[(0,1),(2,1),(3,12)]⟩,⟨4,[(0,3),(2,1)]⟩]))
theorem target0BackwardRoot182_checked : checkTree [(4,3,-66),(-16,-11,306),(-4,-5,54),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot182 = true := by decide

def target0BackwardRoot183 : CoverTree := .split (-1,-1,12) (.split (1,-1,-72) (.leaf 61 [⟨2,[(0,7),(2,1)]⟩,⟨6,[(0,11),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.split (0,-1,-24) (.leaf 58 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩,⟨3,[(1,2),(2,1),(3,18)]⟩]) (.leaf 11 [⟨3,[(1,2),(2,1),(3,18)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1),(6,1)]⟩,⟨5,[(2,1),(4,21),(3,54)]⟩]))) (.split (-1,0,36) (.split (-1,-2,0) (.leaf 11 [⟨1,[(4,3),(6,1)]⟩,⟨1,[(4,1),(5,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 12 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨9,[(1,5),(2,1),(3,72)]⟩,⟨1,[(1,3),(2,1)]⟩])) (.leaf 64 [⟨1,[(0,2),(5,3)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,2),(4,3)]⟩]))
theorem target0BackwardRoot183_checked : checkTree [(-2,-1,54),(-5,-4,90),(16,11,-306),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot183 = true := by decide

theorem targetMeshFamily0Chunk22_covered : FamilyCover targetMeshFamily0Chunk22 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk22,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot176,target0BackwardRoot176_checked⟩
  · exact ⟨target0BackwardRoot177,target0BackwardRoot177_checked⟩
  · exact ⟨target0BackwardRoot178,target0BackwardRoot178_checked⟩
  · exact ⟨target0BackwardRoot179,target0BackwardRoot179_checked⟩
  · exact ⟨target0BackwardRoot180,target0BackwardRoot180_checked⟩
  · exact ⟨target0BackwardRoot181,target0BackwardRoot181_checked⟩
  · exact ⟨target0BackwardRoot182,target0BackwardRoot182_checked⟩
  · exact ⟨target0BackwardRoot183,target0BackwardRoot183_checked⟩

def target0BackwardRoot184 : CoverTree := .split (-1,0,36) (.split (-1,-2,0) (.leaf 11 [⟨2,[(2,1),(5,1),(3,18)]⟩,⟨4,[(2,1),(4,5),(3,6)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 12 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨3,[(1,1),(5,1),(3,18)]⟩,⟨1,[(1,1),(2,1)]⟩])) (.leaf 64 [⟨1,[(0,2),(4,3)]⟩,⟨1,[(4,1)]⟩,⟨3,[(0,1),(2,1)]⟩,⟨1,[(0,3),(2,1)]⟩])
theorem target0BackwardRoot184_checked : checkTree [(-2,-1,54),(-4,-5,54),(5,4,-90),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot184 = true := by decide

def target0BackwardRoot185 : CoverTree := .split (-1,1,36) (.split (0,-1,0) (.leaf 13 [⟨1,[(4,1)]⟩,⟨8,[(0,1),(5,1),(3,30)]⟩,⟨1,[(5,1)]⟩,⟨4,[(0,1),(1,1)]⟩]) (.leaf 17 [⟨4,[(0,1),(1,1)]⟩,⟨1,[(5,1)]⟩,⟨8,[(0,1),(5,7),(3,30)]⟩,⟨8,[(0,7),(1,3),(3,72)]⟩])) (.leaf 12 [⟨4,[(0,1),(2,3)]⟩,⟨12,[(0,5),(2,7)]⟩,⟨15,[(0,2),(4,1),(3,72)]⟩,⟨1,[(4,1)]⟩])
theorem target0BackwardRoot185_checked : checkTree [(-8,-7,162),(16,11,-306),(4,5,-54),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot185 = true := by decide

def target0BackwardRoot186 : CoverTree := .split (1,-1,0) (.split (-2,-1,36) (.leaf 16 [⟨1,[(4,1)]⟩,⟨3,[(1,1),(5,1),(3,18)]⟩,⟨3,[(1,2),(5,5)]⟩,⟨1,[(5,1)]⟩]) (.split (0,-1,0) (.leaf 13 [⟨1,[(1,3),(2,1)]⟩,⟨3,[(0,1),(1,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 17 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨8,[(0,1),(6,7),(3,30)]⟩,⟨2,[(0,1),(5,3),(3,18)]⟩]))) (.split (1,2,-36) (.split (1,0,0) (.leaf 21 [⟨3,[(0,1),(5,2),(3,18)]⟩,⟨7,[(0,1),(6,8),(3,6)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 25 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨3,[(0,1),(1,1)]⟩,⟨1,[(0,3),(1,5)]⟩])) (.leaf 18 [⟨1,[(5,1)]⟩,⟨3,[(1,1),(5,2),(3,18)]⟩,⟨9,[(1,5),(2,1),(3,36)]⟩,⟨1,[(4,1)]⟩]))
theorem target0BackwardRoot186_checked : checkTree [(-8,-7,162),(5,4,-90),(-16,-11,306),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot186 = true := by decide

def target0BackwardRoot187 : CoverTree := .leaf 12 [⟨1,[(0,5),(2,2)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨3,[(1,4),(2,1),(3,30)]⟩]
theorem target0BackwardRoot187_checked : checkTree [(-1,0,36),(0,-1,-12),(3,1,-90),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot187 = true := by decide

def target0BackwardRoot188 : CoverTree := .leaf 12 [⟨3,[(1,1),(2,4),(3,30)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(0,5),(1,2)]⟩]
theorem target0BackwardRoot188_checked : checkTree [(-1,-1,24),(3,2,-78),(0,1,12),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot188 = true := by decide

def target0BackwardRoot189 : CoverTree := .leaf 12 [⟨2,[(0,1),(1,3),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,6)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨1,[(0,5),(2,3)]⟩]
theorem target0BackwardRoot189_checked : checkTree [(2,1,-54),(0,1,12),(-3,-2,78),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot189 = true := by decide

def target0BackwardRoot190 : CoverTree := .leaf 12 [⟨1,[(0,5),(1,3)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨3,[(1,1),(2,2),(3,6)]⟩,⟨2,[(0,1),(2,3),(3,18)]⟩]
theorem target0BackwardRoot190_checked : checkTree [(2,1,-54),(-3,-1,90),(0,-1,-12),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot190 = true := by decide

def target0BackwardRoot191 : CoverTree := .split (-1,1,0) (.split (1,2,-36) (.split (1,0,0) (.leaf 21 [⟨5,[(2,1),(5,4),(3,18)]⟩,⟨13,[(2,1),(6,14),(3,6)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 25 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨6,[(0,1),(2,1)]⟩,⟨2,[(0,9),(2,5)]⟩])) (.leaf 18 [⟨1,[(5,1)]⟩,⟨3,[(1,2),(5,5)]⟩,⟨3,[(1,1),(5,1),(3,18)]⟩,⟨1,[(4,1)]⟩])) (.split (2,1,-36) (.leaf 17 [⟨1,[(5,1)]⟩,⟨9,[(1,7),(2,2),(3,18)]⟩,⟨18,[(1,13),(2,5),(3,72)]⟩,⟨4,[(2,1),(5,5),(3,18)]⟩]) (.leaf 16 [⟨1,[(4,1)]⟩,⟨6,[(0,1),(5,1),(3,54)]⟩,⟨3,[(0,1),(5,4),(3,18)]⟩,⟨1,[(5,1)]⟩]))
theorem target0BackwardRoot191_checked : checkTree [(8,7,-162),(4,5,-90),(-14,-13,306),(0,0,1)] (familyFacets targetKiteFamily0) target0BackwardRoot191 = true := by decide

theorem targetMeshFamily0Chunk23_covered : FamilyCover targetMeshFamily0Chunk23 targetKiteFamily0 := by
  intro p hp
  simp only [targetMeshFamily0Chunk23,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0BackwardRoot184,target0BackwardRoot184_checked⟩
  · exact ⟨target0BackwardRoot185,target0BackwardRoot185_checked⟩
  · exact ⟨target0BackwardRoot186,target0BackwardRoot186_checked⟩
  · exact ⟨target0BackwardRoot187,target0BackwardRoot187_checked⟩
  · exact ⟨target0BackwardRoot188,target0BackwardRoot188_checked⟩
  · exact ⟨target0BackwardRoot189,target0BackwardRoot189_checked⟩
  · exact ⟨target0BackwardRoot190,target0BackwardRoot190_checked⟩
  · exact ⟨target0BackwardRoot191,target0BackwardRoot191_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
