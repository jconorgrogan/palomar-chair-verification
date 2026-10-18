module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1ForwardRoot72 : CoverTree := .split (-4,-5,126) (.split (4,11,-18) (.leaf 174 [⟨1,[(5,1)]⟩,⟨2,[(0,1),(1,3)]⟩,⟨1,[(6,1)]⟩]) (.leaf 173 [⟨1,[(1,6),(3,5),(4,18)]⟩,⟨1,[(6,1)]⟩,⟨1,[(1,24),(5,1)]⟩])) (.split (-7,-8,234) (.split (-16,-19,522) (.split (9,11,-288) (.leaf 184 [⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩,⟨9,[(0,1),(5,2),(4,18)]⟩]) (.split (-17,-21,540) (.leaf 178 [⟨1,[(5,1)]⟩,⟨1,[(9,1)]⟩,⟨9,[(0,1),(5,11),(4,18)]⟩]) (.leaf 179 [⟨1,[(8,1)]⟩,⟨5,[(0,1),(8,4),(4,24)]⟩,⟨1,[(9,1)]⟩]))) (.leaf 185 [⟨1,[(6,1)]⟩,⟨3,[(0,2),(6,5),(4,18)]⟩,⟨1,[(7,1)]⟩])) (.split (10,11,-342) (.split (11,13,-378) (.leaf 200 [⟨3,[(0,1),(3,2)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 199 [⟨3,[(0,1),(3,2)]⟩,⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩])) (.leaf 198 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(0,1),(3,1)]⟩])))
theorem target1ForwardRoot72_checked : checkTree [(1,-1,-36),(1,1,-24),(0,1,12),(-2,-1,72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot72 = true := by decide

def target1ForwardRoot73 : CoverTree := .split (1,1,-36) (.split (4,5,-144) (.split (-1,1,54) (.leaf 194 [⟨1,[(3,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 193 [⟨1,[(2,3),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩])) (.split (-1,1,54) (.leaf 195 [⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.split (-5,-4,198) (.leaf 196 [⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 192 [⟨1,[(2,3),(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(8,1)]⟩])))) (.split (-16,-19,522) (.split (-4,-5,126) (.leaf 174 [⟨1,[(7,1)]⟩,⟨1,[(0,1),(4,18)]⟩,⟨1,[(0,2),(1,9),(4,18)]⟩]) (.split (9,11,-288) (.leaf 184 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(0,1),(1,1)]⟩]) (.split (-17,-21,540) (.leaf 178 [⟨1,[(7,1)]⟩,⟨1,[(9,1)]⟩,⟨3,[(3,1),(7,4)]⟩]) (.leaf 179 [⟨1,[(8,1)]⟩,⟨2,[(0,1),(6,1),(4,6)]⟩,⟨1,[(9,1)]⟩])))) (.split (10,11,-342) (.split (-11,-13,378) (.leaf 199 [⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 200 [⟨1,[(5,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(8,1)]⟩])) (.split (7,8,-234) (.leaf 198 [⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(3,1)]⟩]) (.leaf 185 [⟨1,[(8,1)]⟩,⟨3,[(3,5),(8,4)]⟩,⟨1,[(6,1)]⟩]))))
theorem target1ForwardRoot73_checked : checkTree [(2,1,-72),(0,1,12),(-1,0,48),(-1,-2,36),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot73 = true := by decide

theorem targetKiteFamily1Chunk9_covered : FamilyCover targetKiteFamily1Chunk9 targetMeshFamily1 := by
  intro p hp
  simp only [targetKiteFamily1Chunk9,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨target1ForwardRoot72,target1ForwardRoot72_checked⟩
  · exact ⟨target1ForwardRoot73,target1ForwardRoot73_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
