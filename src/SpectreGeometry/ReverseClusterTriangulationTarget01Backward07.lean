module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1BackwardRoot168 : CoverTree := .split (0,1,24) (.split (-1,-2,0) (.leaf 11 [⟨3,[(0,2),(1,1)]⟩,⟨1,[(4,1)]⟩,⟨4,[(0,1),(4,3),(3,6)]⟩,⟨1,[(5,1)]⟩]) (.split (-1,1,36) (.leaf 13 [⟨1,[(6,1)]⟩,⟨6,[(0,5),(1,1),(3,54)]⟩,⟨3,[(0,7),(1,2),(3,18)]⟩,⟨3,[(0,2),(1,1)]⟩]) (.leaf 12 [⟨1,[(5,1)]⟩,⟨4,[(0,1),(4,3),(3,6)]⟩,⟨6,[(0,5),(1,1),(3,54)]⟩,⟨1,[(6,1)]⟩]))) (.split (-1,1,72) (.leaf 58 [⟨1,[(5,1)]⟩,⟨4,[(0,1),(4,1),(3,6)]⟩,⟨1,[(4,1)]⟩,⟨3,[(0,2),(1,1)]⟩]) (.leaf 61 [⟨3,[(0,13),(2,5)]⟩,⟨1,[(0,3),(2,1)]⟩,⟨4,[(0,1),(4,1),(3,6)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot168_checked : checkTree [(-4,-3,66),(14,9,-240),(11,9,-150),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot168 = true := by decide

def target1BackwardRoot169 : CoverTree := .split (0,1,0) (.split (-1,1,0) (.split (1,2,-36) (.split (1,0,0) (.leaf 21 [⟨2,[(0,1),(4,1),(3,6)]⟩,⟨3,[(0,1),(7,4),(3,6)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 25 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨3,[(0,7),(1,1)]⟩,⟨3,[(0,43),(1,7)]⟩])) (.leaf 18 [⟨1,[(6,1)]⟩,⟨16,[(1,1),(6,9),(3,66)]⟩,⟨25,[(1,1),(4,7),(3,90)]⟩,⟨1,[(5,1)]⟩])) (.leaf 16 [⟨1,[(5,1)]⟩,⟨25,[(1,1),(4,7),(3,90)]⟩,⟨1,[(4,1)]⟩,⟨2,[(0,1),(4,1),(3,6)]⟩])) (.split (-2,-1,36) (.leaf 10 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨25,[(1,1),(4,18),(3,90)]⟩,⟨11,[(1,3),(5,32),(3,18)]⟩]) (.split (1,-1,-36) (.split (-1,-2,0) (.leaf 11 [⟨1,[(5,1)]⟩,⟨27,[(1,14),(2,25),(3,108)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨1,[(7,1)]⟩]) (.leaf 12 [⟨1,[(7,1)]⟩,⟨3,[(1,1),(2,2),(3,18)]⟩,⟨2,[(0,1),(5,1),(3,18)]⟩,⟨1,[(6,1)]⟩])) (.leaf 13 [⟨1,[(6,1)]⟩,⟨2,[(0,1),(5,1),(3,18)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩])))
theorem target1BackwardRoot169_checked : checkTree [(-4,-3,66),(25,18,-390),(-14,-9,240),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot169 = true := by decide

def target1BackwardRoot170 : CoverTree := .split (2,1,-36) (.split (0,-1,0) (.split (-1,1,36) (.leaf 13 [⟨1,[(6,1)]⟩,⟨16,[(0,1),(2,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 12 [⟨4,[(1,1),(5,3),(3,18)]⟩,⟨144,[(1,19),(2,11),(3,576)]⟩,⟨16,[(0,1),(2,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 17 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨20,[(2,1),(5,19),(3,30)]⟩,⟨6,[(2,1),(4,7),(3,18)]⟩])) (.split (-1,1,0) (.split (1,2,-36) (.split (1,0,0) (.leaf 21 [⟨1,[(4,1)]⟩,⟨19,[(2,1),(7,20),(3,6)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 25 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨16,[(0,1),(2,1)]⟩,⟨16,[(0,39),(2,7)]⟩])) (.leaf 18 [⟨1,[(6,1)]⟩,⟨5,[(0,2),(6,3),(3,24)]⟩,⟨2,[(0,1),(4,1),(3,6)]⟩,⟨1,[(5,1)]⟩])) (.split (0,1,0) (.leaf 16 [⟨1,[(5,1)]⟩,⟨2,[(0,1),(4,1),(3,6)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 10 [⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩,⟨4,[(0,1),(6,3),(3,18)]⟩,⟨2,[(0,3),(4,5),(3,18)]⟩])))
theorem target1BackwardRoot170_checked : checkTree [(4,3,-66),(4,11,-18),(-20,-19,450),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot170 = true := by decide

def target1BackwardRoot171 : CoverTree := .split (-1,-2,0) (.split (1,0,-36) (.split (-1,-1,12) (.split (-1,1,72) (.leaf 58 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1),(6,1)]⟩,⟨1,[(0,1),(6,2),(3,6)]⟩]) (.leaf 61 [⟨2,[(0,3),(1,5)]⟩,⟨2,[(0,1),(1,3)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩])) (.leaf 64 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(1,2),(6,3)]⟩])) (.split (0,1,24) (.leaf 11 [⟨5,[(0,3),(4,2),(3,18)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 58 [⟨3,[(0,1),(5,7),(3,30)]⟩,⟨1,[(5,1),(6,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(0,1),(6,1),(3,18)]⟩]))) (.split (1,-1,-36) (.leaf 12 [⟨1,[(4,1)]⟩,⟨3,[(1,2),(4,1)]⟩,⟨3,[(1,2),(5,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 13 [⟨1,[(5,1)]⟩,⟨15,[(2,2),(5,7),(3,72)]⟩,⟨8,[(0,1),(2,1),(3,48)]⟩,⟨16,[(0,9),(2,1)]⟩]))
theorem target1BackwardRoot171_checked : checkTree [(4,3,-66),(-2,-1,54),(-4,-11,18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot171 = true := by decide

def target1BackwardRoot172 : CoverTree := .split (-1,1,72) (.split (-1,-2,0) (.leaf 64 [⟨1,[(5,1)]⟩,⟨3,[(2,2),(5,1)]⟩,⟨3,[(2,2),(4,1)]⟩,⟨1,[(4,1)]⟩]) (.split (1,0,-36) (.leaf 66 [⟨7,[(1,1),(5,6),(3,54)]⟩,⟨19,[(1,1),(6,20),(3,42)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 12 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨18,[(1,1),(2,1),(3,36)]⟩,⟨6,[(1,1),(2,13),(3,36)]⟩]))) (.split (1,1,-12) (.split (0,1,36) (.leaf 65 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨16,[(0,3),(1,1)]⟩]) (.leaf 63 [⟨2,[(0,1),(6,3),(3,18)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1),(6,1)]⟩,⟨2,[(0,1),(2,3)]⟩])) (.split (-1,0,48) (.leaf 61 [⟨1,[(2,2),(6,3)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 63 [⟨5,[(0,1),(5,6),(3,54)]⟩,⟨1,[(5,1),(6,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,2),(6,9)]⟩])))
theorem target1BackwardRoot172_checked : checkTree [(-4,1,234),(-20,-19,450),(2,1,-54),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot172 = true := by decide

def target1BackwardRoot173 : CoverTree := .split (2,1,-72) (.split (-1,1,72) (.leaf 69 [⟨1,[(5,1)]⟩,⟨15,[(1,2),(5,7)]⟩,⟨9,[(1,1),(4,2),(3,18)]⟩,⟨1,[(4,1)]⟩]) (.split (1,2,0) (.leaf 68 [⟨1,[(6,1)]⟩,⟨3,[(0,1),(5,1),(3,18)]⟩,⟨3,[(0,2),(5,5)]⟩,⟨1,[(5,1)]⟩]) (.leaf 67 [⟨1,[(4,1)]⟩,⟨3,[(0,1),(4,2),(3,18)]⟩,⟨3,[(0,1),(5,1),(3,18)]⟩,⟨1,[(6,1)]⟩]))) (.split (1,2,0) (.split (1,0,-36) (.split (0,-1,-12) (.leaf 66 [⟨1,[(4,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 72 [⟨1,[(4,1),(6,3)]⟩,⟨1,[(6,1),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(4,1)]⟩])) (.split (-1,-1,24) (.leaf 12 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨48,[(1,13),(2,5),(3,288)]⟩]) (.leaf 72 [⟨7,[(1,2),(7,15),(3,72)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1),(7,1)]⟩,⟨1,[(4,1)]⟩]))) (.split (1,-1,-72) (.leaf 65 [⟨1,[(6,1)]⟩,⟨18,[(2,1),(4,1),(3,162)]⟩,⟨9,[(2,1),(4,10),(3,54)]⟩,⟨1,[(4,1)]⟩]) (.leaf 64 [⟨1,[(5,1)]⟩,⟨21,[(2,2),(5,19),(3,144)]⟩,⟨18,[(2,1),(4,1),(3,162)]⟩,⟨1,[(6,1)]⟩])))
theorem target1BackwardRoot173_checked : checkTree [(-4,1,234),(-4,-11,18),(20,19,-450),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot173 = true := by decide

def target1BackwardRoot174 : CoverTree := .split (1,-1,-36) (.split (-2,-1,72) (.split (1,1,-24) (.split (0,1,12) (.leaf 72 [⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 66 [⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1),(7,1)]⟩,⟨1,[(5,1),(6,3)]⟩])) (.leaf 12 [⟨5,[(2,1),(4,1),(3,54)]⟩,⟨7,[(2,1),(6,11),(3,6)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩])) (.split (0,-1,-12) (.leaf 69 [⟨8,[(0,5),(2,3)]⟩,⟨24,[(0,7),(2,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 73 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨4,[(0,1),(6,5),(3,6)]⟩,⟨2,[(0,1),(1,1)]⟩]))) (.leaf 15 [⟨2,[(0,1),(1,1)]⟩,⟨6,[(0,1),(1,5)]⟩,⟨3,[(1,2),(4,1)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot174_checked : checkTree [(-4,-5,126),(2,1,-54),(4,11,-18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot174 = true := by decide

def target1BackwardRoot175 : CoverTree := .split (-1,-2,36) (.split (-1,0,24) (.split (2,1,-36) (.split (0,1,0) (.leaf 17 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 13 [⟨1,[(5,3),(6,1)]⟩,⟨1,[(5,1),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩])) (.split (1,-1,0) (.leaf 16 [⟨1,[(7,1)]⟩,⟨18,[(1,1),(2,1),(3,180)]⟩,⟨9,[(1,1),(6,10),(3,90)]⟩,⟨1,[(6,1)]⟩]) (.leaf 18 [⟨1,[(4,1)]⟩,⟨21,[(1,2),(4,19),(3,216)]⟩,⟨18,[(1,1),(2,1),(3,180)]⟩,⟨1,[(7,1)]⟩]))) (.split (1,1,-24) (.leaf 15 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(2,2),(6,3)]⟩]) (.split (-1,1,36) (.leaf 13 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1),(6,1)]⟩,⟨1,[(5,3),(7,1)]⟩]) (.leaf 12 [⟨6,[(1,1),(2,7),(3,72)]⟩,⟨18,[(1,1),(2,19),(3,72)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩])))) (.split (-2,-1,36) (.split (0,-1,24) (.split (1,0,0) (.leaf 21 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 25 [⟨1,[(4,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1),(7,1)]⟩,⟨1,[(4,1),(6,3)]⟩])) (.split (1,1,-24) (.leaf 23 [⟨1,[(0,2),(7,9)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 25 [⟨1,[(4,1)]⟩,⟨1,[(6,1),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,2),(7,39)]⟩]))) (.split (1,-1,0) (.leaf 19 [⟨1,[(4,1)]⟩,⟨3,[(0,2),(4,5)]⟩,⟨3,[(0,1),(4,1),(3,18)]⟩,⟨1,[(6,1)]⟩]) (.leaf 20 [⟨1,[(6,1)]⟩,⟨3,[(0,1),(4,1),(3,18)]⟩,⟨3,[(0,1),(5,2),(3,18)]⟩,⟨1,[(5,1)]⟩])))
theorem target1BackwardRoot175_checked : checkTree [(-4,-5,126),(20,19,-450),(-2,-1,54),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot175 = true := by decide

theorem targetMeshFamily1Chunk21_covered : FamilyCover targetMeshFamily1Chunk21 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk21,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot168,target1BackwardRoot168_checked⟩
  · exact ⟨target1BackwardRoot169,target1BackwardRoot169_checked⟩
  · exact ⟨target1BackwardRoot170,target1BackwardRoot170_checked⟩
  · exact ⟨target1BackwardRoot171,target1BackwardRoot171_checked⟩
  · exact ⟨target1BackwardRoot172,target1BackwardRoot172_checked⟩
  · exact ⟨target1BackwardRoot173,target1BackwardRoot173_checked⟩
  · exact ⟨target1BackwardRoot174,target1BackwardRoot174_checked⟩
  · exact ⟨target1BackwardRoot175,target1BackwardRoot175_checked⟩

def target1BackwardRoot176 : CoverTree := .split (1,-1,36) (.split (0,1,-24) (.leaf 23 [⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(2,2),(5,7),(3,36)]⟩]) (.split (-2,-1,36) (.leaf 21 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1),(5,1)]⟩,⟨1,[(0,3),(6,1)]⟩]) (.leaf 20 [⟨3,[(1,11),(2,16),(3,12)]⟩,⟨3,[(1,1),(2,2),(3,24)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]))) (.leaf 22 [⟨1,[(0,4),(2,1),(3,12)]⟩,⟨1,[(0,6),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩])
theorem target1BackwardRoot176_checked : checkTree [(1,1,-24),(7,9,-228),(-5,-6,156),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot176 = true := by decide

def target1BackwardRoot177 : CoverTree := .split (2,1,-36) (.split (-1,1,0) (.leaf 20 [⟨1,[(5,1)]⟩,⟨1,[(0,1),(1,1),(3,6)]⟩,⟨7,[(1,2),(4,5),(3,36)]⟩,⟨1,[(4,1)]⟩]) (.leaf 19 [⟨1,[(0,4),(1,3)]⟩,⟨1,[(0,6),(1,5)]⟩,⟨1,[(0,1),(1,1),(3,6)]⟩,⟨1,[(5,1)]⟩])) (.split (0,-1,24) (.leaf 21 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨4,[(0,1),(5,5),(3,6)]⟩,⟨1,[(0,4),(1,3)]⟩]) (.leaf 23 [⟨1,[(0,16),(2,9)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]))
theorem target1BackwardRoot177_checked : checkTree [(4,5,-126),(-5,-6,156),(-7,-9,228),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot177 = true := by decide

def target1BackwardRoot178 : CoverTree := .split (-1,1,36) (.split (-1,-2,36) (.leaf 15 [⟨1,[(5,1)]⟩,⟨2,[(2,1),(5,3)]⟩,⟨3,[(0,1),(5,1),(3,18)]⟩,⟨1,[(4,1)]⟩]) (.split (-1,0,24) (.split (1,-1,0) (.leaf 19 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,4),(1,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 20 [⟨1,[(7,1)]⟩,⟨1,[(0,4),(1,1)]⟩,⟨3,[(1,5),(2,17),(3,24)]⟩,⟨3,[(1,7),(2,25),(3,12)]⟩])) (.leaf 14 [⟨13,[(1,3),(5,25),(3,216)]⟩,⟨21,[(1,1),(6,17),(3,120)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]))) (.split (2,1,-72) (.split (0,1,12) (.leaf 73 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨17,[(1,1),(6,21),(3,24)]⟩,⟨25,[(1,3),(5,13),(3,216)]⟩]) (.leaf 69 [⟨1,[(0,38),(1,9)]⟩,⟨1,[(0,4),(1,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩])) (.leaf 72 [⟨1,[(4,1)]⟩,⟨3,[(1,1),(2,4),(3,12)]⟩,⟨3,[(0,1),(5,2),(3,18)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot178_checked : checkTree [(4,5,-126),(-17,-21,540),(5,6,-156),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot178 = true := by decide

def target1BackwardRoot179 : CoverTree := .split (-1,-2,36) (.split (1,-1,-36) (.split (2,1,-72) (.split (0,1,12) (.leaf 73 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨7,[(1,1),(7,9)]⟩,⟨1,[(4,1)]⟩]) (.leaf 69 [⟨1,[(0,19),(2,10)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 72 [⟨1,[(5,1)]⟩,⟨3,[(1,2),(2,1),(3,12)]⟩,⟨25,[(2,2),(6,17),(3,156)]⟩,⟨1,[(6,1)]⟩])) (.leaf 15 [⟨1,[(4,1)]⟩,⟨13,[(2,2),(4,21),(3,12)]⟩,⟨3,[(1,2),(2,1),(3,12)]⟩,⟨1,[(5,1)]⟩])) (.split (-1,0,24) (.split (1,-1,0) (.leaf 19 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 20 [⟨1,[(6,1)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨6,[(1,17),(2,7),(3,48)]⟩,⟨6,[(1,25),(2,11),(3,24)]⟩])) (.leaf 14 [⟨5,[(1,3),(4,11),(3,72)]⟩,⟨9,[(1,1),(5,7),(3,48)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]))
theorem target1BackwardRoot179_checked : checkTree [(-9,-11,288),(-7,-9,228),(17,21,-540),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot179 = true := by decide

def target1BackwardRoot180 : CoverTree := .split (-2,-1,36) (.split (0,1,-24) (.split (1,-1,36) (.leaf 23 [⟨1,[(6,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 22 [⟨1,[(0,4),(1,7),(3,12)]⟩,⟨1,[(0,6),(1,11)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(6,1)]⟩])) (.leaf 21 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(1,1),(5,6),(3,12)]⟩,⟨4,[(0,5),(2,7),(3,12)]⟩])) (.split (-1,1,0) (.leaf 20 [⟨1,[(5,1)]⟩,⟨2,[(0,1),(2,1),(3,12)]⟩,⟨13,[(0,2),(4,9),(3,60)]⟩,⟨1,[(4,1)]⟩]) (.leaf 19 [⟨4,[(0,5),(2,7),(3,12)]⟩,⟨4,[(0,9),(2,11),(3,12)]⟩,⟨2,[(0,1),(2,1),(3,12)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot180_checked : checkTree [(-9,-11,288),(5,6,-156),(7,9,-228),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot180 = true := by decide

def target1BackwardRoot181 : CoverTree := .split (-2,-1,36) (.split (0,1,-24) (.leaf 23 [⟨2,[(0,7),(1,1),(3,6)]⟩,⟨10,[(0,3),(1,1),(3,30)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 21 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨16,[(1,1),(5,19),(3,66)]⟩,⟨3,[(1,1),(2,13),(3,24)]⟩])) (.split (-1,1,0) (.leaf 20 [⟨1,[(5,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(2,2),(4,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 19 [⟨3,[(1,1),(2,13),(3,24)]⟩,⟨3,[(1,1),(2,19),(3,24)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot181_checked : checkTree [(-2,-3,84),(16,19,-522),(-1,-1,30),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot181 = true := by decide

def target1BackwardRoot182 : CoverTree := .split (0,1,-24) (.split (1,-1,36) (.leaf 23 [⟨1,[(5,1)]⟩,⟨5,[(0,3),(1,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,1),(4,2)]⟩]) (.leaf 22 [⟨5,[(0,8),(1,1),(3,60)]⟩,⟨5,[(0,14),(1,3)]⟩,⟨5,[(0,3),(1,1)]⟩,⟨1,[(5,1)]⟩])) (.split (2,1,-36) (.split (-1,1,0) (.leaf 20 [⟨1,[(6,1)]⟩,⟨5,[(0,2),(6,1),(3,12)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 19 [⟨15,[(1,13),(2,8),(3,120)]⟩,⟨15,[(1,19),(2,14),(3,120)]⟩,⟨5,[(1,1),(2,1),(3,30)]⟩,⟨1,[(6,1)]⟩])) (.leaf 21 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨11,[(1,1),(4,14),(3,36)]⟩,⟨15,[(1,13),(2,8),(3,120)]⟩]))
theorem target1BackwardRoot182_checked : checkTree [(-2,-3,84),(11,14,-372),(-16,-19,522),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot182 = true := by decide

def target1BackwardRoot183 : CoverTree := .split (2,1,-36) (.split (-1,1,0) (.leaf 20 [⟨1,[(5,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨1,[(1,2),(4,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 19 [⟨2,[(0,1),(1,7),(3,6)]⟩,⟨2,[(0,1),(1,11),(3,6)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨1,[(5,1)]⟩])) (.split (0,1,-24) (.split (1,-1,36) (.leaf 23 [⟨1,[(6,1)]⟩,⟨5,[(0,3),(2,2)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 22 [⟨5,[(0,8),(2,7),(3,60)]⟩,⟨5,[(0,14),(2,11)]⟩,⟨5,[(0,3),(2,2)]⟩,⟨1,[(6,1)]⟩])) (.leaf 21 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨9,[(0,1),(5,11),(3,24)]⟩,⟨2,[(0,1),(1,7),(3,6)]⟩]))
theorem target1BackwardRoot183_checked : checkTree [(9,11,-288),(-1,-1,30),(-11,-14,372),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot183 = true := by decide

theorem targetMeshFamily1Chunk22_covered : FamilyCover targetMeshFamily1Chunk22 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk22,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot176,target1BackwardRoot176_checked⟩
  · exact ⟨target1BackwardRoot177,target1BackwardRoot177_checked⟩
  · exact ⟨target1BackwardRoot178,target1BackwardRoot178_checked⟩
  · exact ⟨target1BackwardRoot179,target1BackwardRoot179_checked⟩
  · exact ⟨target1BackwardRoot180,target1BackwardRoot180_checked⟩
  · exact ⟨target1BackwardRoot181,target1BackwardRoot181_checked⟩
  · exact ⟨target1BackwardRoot182,target1BackwardRoot182_checked⟩
  · exact ⟨target1BackwardRoot183,target1BackwardRoot183_checked⟩

def target1BackwardRoot184 : CoverTree := .split (-1,-2,36) (.split (1,-1,-36) (.split (2,1,-72) (.split (0,1,12) (.leaf 73 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨16,[(1,1),(7,19),(3,18)]⟩,⟨1,[(4,1)]⟩]) (.leaf 69 [⟨1,[(0,7),(1,4)]⟩,⟨5,[(0,3),(1,2)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 72 [⟨1,[(5,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(2,2),(6,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 15 [⟨1,[(4,1)]⟩,⟨1,[(2,2),(4,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(5,1)]⟩])) (.split (-1,0,24) (.leaf 19 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,3),(1,2)]⟩,⟨3,[(1,2),(2,35),(3,6)]⟩]) (.leaf 14 [⟨13,[(1,3),(4,22),(3,162)]⟩,⟨19,[(1,1),(5,16),(3,90)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]))
theorem target1BackwardRoot184_checked : checkTree [(9,11,-288),(-16,-19,522),(1,1,-30),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot184 = true := by decide

def target1BackwardRoot185 : CoverTree := .split (-1,1,36) (.split (-1,-2,36) (.leaf 15 [⟨1,[(5,1)]⟩,⟨13,[(2,2),(5,19),(3,48)]⟩,⟨5,[(1,1),(2,1),(3,30)]⟩,⟨1,[(4,1)]⟩]) (.split (1,0,-24) (.leaf 14 [⟨2,[(0,1),(5,3),(3,18)]⟩,⟨8,[(0,1),(6,7),(3,30)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 19 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨5,[(0,3),(2,1)]⟩,⟨3,[(1,7),(2,5),(3,6)]⟩]))) (.split (2,1,-72) (.split (0,1,12) (.leaf 73 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨7,[(0,1),(6,8),(3,6)]⟩,⟨3,[(0,1),(5,2),(3,18)]⟩]) (.leaf 69 [⟨1,[(0,7),(2,3)]⟩,⟨5,[(0,3),(2,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩])) (.leaf 72 [⟨1,[(4,1)]⟩,⟨5,[(1,1),(2,1),(3,30)]⟩,⟨11,[(2,1),(5,8),(3,78)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot185_checked : checkTree [(-7,-8,234),(-11,-14,372),(16,19,-522),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot185 = true := by decide

def target1BackwardRoot186 : CoverTree := .split (1,-1,0) (.split (-1,0,24) (.leaf 19 [⟨1,[(1,2),(5,1)]⟩,⟨1,[(5,1)]⟩,⟨8,[(0,1),(5,1),(3,30)]⟩,⟨1,[(4,1)]⟩]) (.leaf 14 [⟨10,[(0,17),(2,9),(3,90)]⟩,⟨8,[(0,1),(5,7),(3,30)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,4),(2,3)]⟩])) (.leaf 20 [⟨1,[(4,1)]⟩,⟨10,[(0,3),(2,1),(3,30)]⟩,⟨1,[(0,1),(1,7)]⟩,⟨1,[(0,1),(1,9)]⟩])
theorem target1BackwardRoot186_checked : checkTree [(-7,-8,234),(1,1,-30),(11,14,-372),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot186 = true := by decide

def target1BackwardRoot187 : CoverTree := .leaf 71 [⟨3,[(1,8),(2,1),(3,6)]⟩,⟨3,[(1,2),(2,1),(3,6)]⟩,⟨1,[(0,3),(2,2)]⟩,⟨1,[(0,7),(2,4)]⟩]
theorem target1BackwardRoot187_checked : checkTree [(-3,-1,144),(-1,-1,42),(5,2,-234),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot187 = true := by decide

def target1BackwardRoot188 : CoverTree := .split (1,2,-36) (.leaf 70 [⟨1,[(0,2),(1,1),(3,12)]⟩,⟨1,[(0,4),(1,3)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 71 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,2),(3,12)]⟩])
theorem target1BackwardRoot188_checked : checkTree [(-3,-1,144),(4,1,-192),(1,1,-42),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot188 = true := by decide

def target1BackwardRoot189 : CoverTree := .split (1,2,-36) (.leaf 70 [⟨1,[(0,2),(2,1),(3,12)]⟩,⟨1,[(0,4),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 71 [⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨3,[(1,5),(2,2),(3,42)]⟩])
theorem target1BackwardRoot189_checked : checkTree [(1,0,-48),(1,1,-42),(-4,-1,192),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot189 = true := by decide

def target1BackwardRoot190 : CoverTree := .leaf 71 [⟨1,[(0,1),(2,3)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨2,[(0,3),(1,1),(3,6)]⟩,⟨2,[(0,5),(1,3),(3,18)]⟩]
theorem target1BackwardRoot190_checked : checkTree [(2,1,-90),(-4,-1,192),(-1,-1,42),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot190 = true := by decide

def target1BackwardRoot191 : CoverTree := .leaf 71 [⟨3,[(1,7),(2,8),(3,6)]⟩,⟨3,[(1,1),(2,2),(3,6)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,7),(1,3)]⟩]
theorem target1BackwardRoot191_checked : checkTree [(2,1,-90),(-5,-2,234),(4,1,-192),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot191 = true := by decide

theorem targetMeshFamily1Chunk23_covered : FamilyCover targetMeshFamily1Chunk23 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk23,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot184,target1BackwardRoot184_checked⟩
  · exact ⟨target1BackwardRoot185,target1BackwardRoot185_checked⟩
  · exact ⟨target1BackwardRoot186,target1BackwardRoot186_checked⟩
  · exact ⟨target1BackwardRoot187,target1BackwardRoot187_checked⟩
  · exact ⟨target1BackwardRoot188,target1BackwardRoot188_checked⟩
  · exact ⟨target1BackwardRoot189,target1BackwardRoot189_checked⟩
  · exact ⟨target1BackwardRoot190,target1BackwardRoot190_checked⟩
  · exact ⟨target1BackwardRoot191,target1BackwardRoot191_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
