module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1BackwardRoot216 : CoverTree := .leaf 20 [⟨2,[(0,1),(1,3),(3,18)]⟩,⟨3,[(1,2),(2,1),(3,6)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨1,[(0,5),(2,3)]⟩]
theorem target1BackwardRoot216_checked : checkTree [(1,2,-54),(-1,0,12),(-1,-3,78),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot216 = true := by decide

def target1BackwardRoot217 : CoverTree := .leaf 20 [⟨1,[(0,5),(1,3)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨3,[(1,1),(2,2),(3,6)]⟩,⟨2,[(0,1),(2,3),(3,18)]⟩]
theorem target1BackwardRoot217_checked : checkTree [(1,2,-54),(-2,-3,90),(1,0,-12),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot217 = true := by decide

theorem targetMeshFamily1Chunk27_covered : FamilyCover targetMeshFamily1Chunk27 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk27,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨target1BackwardRoot216,target1BackwardRoot216_checked⟩
  · exact ⟨target1BackwardRoot217,target1BackwardRoot217_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
