module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1BackwardRoot120 : CoverTree := .split (-2,-1,-36) (.split (0,-1,0) (.split (1,2,36) (.leaf 35 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 36 [⟨1,[(6,1)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨3,[(0,11),(2,10)]⟩,⟨3,[(0,5),(2,4),(3,36)]⟩])) (.leaf 27 [⟨3,[(0,1),(1,2),(3,36)]⟩,⟨5,[(1,1),(5,8),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.split (-1,-2,0) (.leaf 28 [⟨1,[(4,1)]⟩,⟨13,[(0,2),(4,7),(3,12)]⟩,⟨2,[(0,1),(1,1),(3,6)]⟩,⟨1,[(5,1)]⟩]) (.leaf 29 [⟨1,[(5,1)]⟩,⟨2,[(0,1),(1,1),(3,6)]⟩,⟨3,[(0,4),(1,5),(3,18)]⟩,⟨3,[(0,1),(1,2),(3,36)]⟩]))
theorem target1BackwardRoot120_checked : checkTree [(-7,3,-132),(5,-3,102),(8,-3,156),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot120 = true := by decide

def target1BackwardRoot121 : CoverTree := .split (1,1,0) (.split (-2,-1,0) (.leaf 33 [⟨3,[(0,7),(1,4)]⟩,⟨1,[(4,1)]⟩,⟨8,[(2,1),(4,5),(3,6)]⟩,⟨1,[(5,1)]⟩]) (.split (1,2,-36) (.leaf 25 [⟨1,[(6,1)]⟩,⟨1,[(0,2),(1,1),(3,6)]⟩,⟨3,[(0,19),(1,10)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 24 [⟨1,[(5,1)]⟩,⟨8,[(2,1),(4,5),(3,6)]⟩,⟨1,[(0,2),(1,1),(3,6)]⟩,⟨1,[(6,1)]⟩]))) (.split (1,2,0) (.leaf 29 [⟨1,[(5,1)]⟩,⟨8,[(2,1),(4,3),(3,6)]⟩,⟨1,[(4,1)]⟩,⟨3,[(0,7),(1,4)]⟩]) (.leaf 28 [⟨9,[(1,11),(2,25),(3,36)]⟩,⟨9,[(1,5),(2,13),(3,36)]⟩,⟨8,[(2,1),(4,3),(3,6)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot121_checked : checkTree [(-7,3,-132),(13,-6,258),(-5,3,-102),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot121 = true := by decide

def target1BackwardRoot122 : CoverTree := .split (0,1,-12) (.split (-2,-1,0) (.split (1,1,0) (.leaf 33 [⟨1,[(0,1),(2,2)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 29 [⟨7,[(0,1),(4,17),(3,72)]⟩,⟨1,[(4,1),(6,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,1),(2,2)]⟩])) (.split (1,2,-36) (.leaf 25 [⟨1,[(6,1)]⟩,⟨2,[(0,1),(2,3),(3,12)]⟩,⟨1,[(0,2),(2,5)]⟩,⟨1,[(0,1),(2,2)]⟩]) (.leaf 24 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨2,[(0,1),(2,3),(3,12)]⟩,⟨1,[(6,1)]⟩]))) (.split (1,2,0) (.leaf 29 [⟨1,[(5,1)]⟩,⟨3,[(2,1),(4,1)]⟩,⟨3,[(2,1),(4,4)]⟩,⟨1,[(0,1),(2,2)]⟩]) (.leaf 28 [⟨6,[(1,5),(2,11),(3,24)]⟩,⟨2,[(1,1),(2,3)]⟩,⟨3,[(2,1),(4,1)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot122_checked : checkTree [(7,-3,132),(9,-1,144),(-3,1,-48),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot122 = true := by decide

def target1BackwardRoot123 : CoverTree := .split (-2,-1,-36) (.split (1,2,36) (.split (0,-1,0) (.leaf 35 [⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩,⟨5,[(0,2),(1,3)]⟩,⟨1,[(5,1)]⟩]) (.leaf 27 [⟨5,[(0,2),(2,1),(3,60)]⟩,⟨7,[(0,1),(6,10),(3,36)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩])) (.leaf 36 [⟨1,[(5,1)]⟩,⟨5,[(0,2),(1,3)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨5,[(0,1),(1,4),(3,60)]⟩])) (.split (0,1,0) (.split (-1,-2,0) (.leaf 28 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨4,[(1,1),(6,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 29 [⟨1,[(6,1)]⟩,⟨20,[(0,1),(2,3),(3,60)]⟩,⟨2,[(0,1),(2,1),(3,12)]⟩,⟨5,[(0,2),(2,1),(3,60)]⟩])) (.leaf 1 [⟨5,[(0,1),(1,4),(3,60)]⟩,⟨3,[(1,1),(5,5),(3,12)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]))
theorem target1BackwardRoot123_checked : checkTree [(7,-3,132),(-3,2,-48),(-9,1,-144),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot123 = true := by decide

def target1BackwardRoot124 : CoverTree := .split (-1,-2,-36) (.leaf 36 [⟨1,[(4,1)]⟩,⟨5,[(0,2),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨5,[(0,4),(1,1)]⟩]) (.split (-2,-1,-36) (.leaf 35 [⟨1,[(5,1)]⟩,⟨5,[(1,1),(2,3)]⟩,⟨4,[(2,1),(4,1),(3,12)]⟩,⟨1,[(4,1)]⟩]) (.leaf 1 [⟨5,[(0,4),(1,1)]⟩,⟨3,[(1,1),(2,2),(3,12)]⟩,⟨5,[(1,1),(2,3)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot124_checked : checkTree [(1,1,36),(-9,1,-144),(3,-2,48),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot124 = true := by decide

def target1BackwardRoot125 : CoverTree := .split (2,1,36) (.split (0,-1,0) (.leaf 1 [⟨2,[(0,1),(4,1),(3,18)]⟩,⟨4,[(0,1),(5,5),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 28 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨5,[(0,2),(1,1)]⟩,⟨5,[(0,8),(1,9)]⟩])) (.split (1,2,36) (.leaf 35 [⟨1,[(4,1)]⟩,⟨7,[(1,2),(4,3),(3,12)]⟩,⟨4,[(1,1),(5,1),(3,12)]⟩,⟨1,[(5,1)]⟩]) (.leaf 36 [⟨1,[(5,1)]⟩,⟨5,[(0,1),(2,1),(3,30)]⟩,⟨1,[(0,2),(2,1)]⟩,⟨5,[(0,8),(2,3)]⟩]))
theorem target1BackwardRoot125_checked : checkTree [(-4,1,-54),(3,-2,48),(9,-1,144),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot125 = true := by decide

def target1BackwardRoot126 : CoverTree := .split (1,1,0) (.split (-2,-1,0) (.split (0,1,-12) (.leaf 33 [⟨1,[(0,2),(1,3)]⟩,⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 31 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1),(6,1)]⟩,⟨1,[(4,3),(5,1)]⟩])) (.split (1,2,-36) (.leaf 25 [⟨1,[(6,1)]⟩,⟨1,[(0,1),(1,1),(3,6)]⟩,⟨1,[(0,4),(1,5)]⟩,⟨1,[(0,2),(1,3)]⟩]) (.leaf 24 [⟨1,[(5,1)]⟩,⟨3,[(0,1),(5,2),(3,18)]⟩,⟨1,[(0,1),(1,1),(3,6)]⟩,⟨1,[(6,1)]⟩]))) (.split (1,2,0) (.split (-1,0,-12) (.leaf 29 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(0,2),(1,3)]⟩]) (.leaf 31 [⟨1,[(4,3),(5,1)]⟩,⟨1,[(4,1),(6,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩])) (.leaf 28 [⟨3,[(1,7),(2,5),(3,12)]⟩,⟨1,[(1,1),(2,1)]⟩,⟨4,[(2,1),(5,1)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot126_checked : checkTree [(-4,1,-54),(3,-1,48),(-3,2,-48),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot126 = true := by decide

def target1BackwardRoot127 : CoverTree := .split (1,2,0) (.split (0,1,-12) (.split (2,1,0) (.split (-1,-2,36) (.leaf 24 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(7,1)]⟩]) (.leaf 25 [⟨1,[(7,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,5)]⟩,⟨1,[(0,1),(2,3)]⟩])) (.leaf 33 [⟨1,[(0,1),(2,3)]⟩,⟨4,[(0,1),(5,5),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 31 [⟨1,[(2,2),(5,1)]⟩,⟨1,[(5,1)]⟩,⟨7,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩])) (.split (1,1,12) (.leaf 3 [⟨1,[(4,1)]⟩,⟨5,[(1,2),(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(2,2),(5,1)]⟩]) (.split (1,-1,0) (.leaf 0 [⟨1,[(1,2),(2,5),(3,6)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 1 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨2,[(1,1),(5,3),(3,6)]⟩,⟨1,[(1,1),(2,1),(3,12)]⟩])))
theorem target1BackwardRoot127_checked : checkTree [(4,-1,54),(3,1,30),(-1,0,-6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot127 = true := by decide

theorem targetMeshFamily1Chunk15_covered : FamilyCover targetMeshFamily1Chunk15 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk15,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot120,target1BackwardRoot120_checked⟩
  · exact ⟨target1BackwardRoot121,target1BackwardRoot121_checked⟩
  · exact ⟨target1BackwardRoot122,target1BackwardRoot122_checked⟩
  · exact ⟨target1BackwardRoot123,target1BackwardRoot123_checked⟩
  · exact ⟨target1BackwardRoot124,target1BackwardRoot124_checked⟩
  · exact ⟨target1BackwardRoot125,target1BackwardRoot125_checked⟩
  · exact ⟨target1BackwardRoot126,target1BackwardRoot126_checked⟩
  · exact ⟨target1BackwardRoot127,target1BackwardRoot127_checked⟩

def target1BackwardRoot128 : CoverTree := .split (2,1,36) (.split (-1,1,0) (.split (-1,-1,-12) (.split (0,-1,0) (.leaf 1 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 28 [⟨1,[(4,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1),(7,1)]⟩,⟨1,[(4,1),(6,3)]⟩])) (.split (1,0,12) (.leaf 3 [⟨1,[(2,2),(7,5)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 28 [⟨1,[(4,1)]⟩,⟨1,[(6,1),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(0,2),(7,9)]⟩]))) (.split (1,2,36) (.leaf 0 [⟨1,[(6,1)]⟩,⟨5,[(2,2),(6,1),(3,24)]⟩,⟨2,[(2,1),(5,1),(3,6)]⟩,⟨1,[(5,1)]⟩]) (.leaf 34 [⟨1,[(4,1)]⟩,⟨1,[(1,1),(5,1),(3,6)]⟩,⟨2,[(1,1),(6,1),(3,18)]⟩,⟨1,[(6,1)]⟩]))) (.split (-1,1,0) (.split (-1,-2,-36) (.leaf 36 [⟨1,[(6,1)]⟩,⟨3,[(0,1),(5,1),(3,18)]⟩,⟨3,[(0,2),(5,5)]⟩,⟨1,[(5,1)]⟩]) (.leaf 35 [⟨1,[(4,1)]⟩,⟨3,[(0,1),(4,2),(3,18)]⟩,⟨3,[(0,1),(5,1),(3,18)]⟩,⟨1,[(6,1)]⟩])) (.leaf 37 [⟨1,[(5,1)]⟩,⟨1,[(1,2),(5,3)]⟩,⟨1,[(1,1),(5,1),(3,6)]⟩,⟨1,[(4,1)]⟩]))
theorem target1BackwardRoot128_checked : checkTree [(4,-1,54),(-1,2,18),(-3,-1,-30),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot128 = true := by decide

def target1BackwardRoot129 : CoverTree := .split (0,1,24) (.split (-2,-1,-36) (.split (1,1,36) (.leaf 37 [⟨3,[(2,2),(6,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 39 [⟨2,[(0,1),(1,3)]⟩,⟨1,[(4,1),(6,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,2),(6,9)]⟩])) (.split (-1,-2,-36) (.leaf 34 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨1,[(6,1)]⟩]) (.leaf 0 [⟨1,[(6,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨2,[(1,3),(2,1),(3,12)]⟩,⟨4,[(2,3),(6,1),(3,18)]⟩]))) (.split (1,0,12) (.leaf 41 [⟨1,[(1,2),(4,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨2,[(0,1),(1,3)]⟩]) (.leaf 39 [⟨2,[(0,1),(1,3)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1),(5,1)]⟩,⟨5,[(0,1),(4,9),(3,54)]⟩]))
theorem target1BackwardRoot129_checked : checkTree [(5,4,162),(-1,0,-6),(1,-2,-18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot129 = true := by decide

def target1BackwardRoot130 : CoverTree := .split (2,1,36) (.split (0,-1,-24) (.split (-1,1,36) (.leaf 40 [⟨1,[(6,1)]⟩,⟨3,[(1,1),(5,2),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩]) (.split (-1,-2,-72) (.leaf 53 [⟨1,[(4,1)]⟩,⟨1,[(1,2),(4,3)]⟩,⟨1,[(1,1),(4,1),(3,6)]⟩,⟨1,[(7,1)]⟩]) (.leaf 50 [⟨1,[(7,1)]⟩,⟨1,[(1,1),(4,1),(3,6)]⟩,⟨2,[(1,1),(6,1),(3,18)]⟩,⟨1,[(6,1)]⟩]))) (.split (-1,-2,-36) (.leaf 34 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨3,[(1,1),(5,1),(3,6)]⟩,⟨1,[(6,1)]⟩]) (.leaf 0 [⟨1,[(6,1)]⟩,⟨3,[(1,1),(5,1),(3,6)]⟩,⟨1,[(1,1),(2,2),(3,6)]⟩,⟨1,[(1,1),(2,4),(3,6)]⟩]))) (.split (1,2,72) (.leaf 41 [⟨1,[(4,1)]⟩,⟨1,[(2,2),(4,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(5,1)]⟩]) (.split (1,-1,-36) (.leaf 52 [⟨1,[(6,1)]⟩,⟨3,[(0,1),(4,1),(3,18)]⟩,⟨3,[(0,2),(4,5)]⟩,⟨1,[(4,1)]⟩]) (.leaf 51 [⟨1,[(5,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(2,2),(6,1)]⟩,⟨1,[(6,1)]⟩])))
theorem target1BackwardRoot130_checked : checkTree [(5,4,162),(-3,-1,-30),(1,0,6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot130 = true := by decide

def target1BackwardRoot131 : CoverTree := .split (1,0,0) (.split (-1,-1,-24) (.split (-1,1,36) (.leaf 40 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1),(5,1)]⟩,⟨1,[(4,3),(6,1)]⟩]) (.split (-1,-2,-72) (.leaf 53 [⟨7,[(0,1),(2,9)]⟩,⟨7,[(0,3),(2,13)]⟩,⟨7,[(0,1),(2,2),(3,42)]⟩,⟨1,[(7,1)]⟩]) (.leaf 50 [⟨1,[(7,1)]⟩,⟨7,[(0,1),(2,2),(3,42)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]))) (.split (-1,-2,-36) (.leaf 43 [⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨11,[(0,2),(5,15),(3,72)]⟩]) (.split (0,-1,-12) (.leaf 7 [⟨2,[(0,1),(4,9),(3,18)]⟩,⟨1,[(7,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 4 [⟨1,[(1,1),(7,1),(3,6)]⟩,⟨1,[(4,1),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨2,[(0,1),(4,9),(3,18)]⟩])))) (.split (1,2,36) (.split (-1,-1,-12) (.leaf 0 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩,⟨4,[(1,3),(5,1),(3,18)]⟩]) (.leaf 4 [⟨3,[(1,2),(6,1),(3,24)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1),(6,1)]⟩,⟨2,[(1,1),(4,5),(3,18)]⟩])) (.split (0,1,24) (.leaf 34 [⟨1,[(2,1),(4,1),(3,6)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 40 [⟨1,[(2,1),(4,4),(3,6)]⟩,⟨1,[(4,1),(6,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(2,1),(4,1),(3,6)]⟩])))
theorem target1BackwardRoot131_checked : checkTree [(-13,-2,-18),(1,-2,-18),(3,1,30),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot131 = true := by decide

def target1BackwardRoot132 : CoverTree := .split (1,2,0) (.split (0,-1,12) (.split (-2,-1,0) (.leaf 31 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨1,[(4,1)]⟩]) (.leaf 30 [⟨3,[(0,1),(6,5),(3,18)]⟩,⟨13,[(0,1),(5,11),(3,42)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩])) (.split (-1,-2,36) (.leaf 24 [⟨1,[(1,2),(5,1)]⟩,⟨1,[(5,1)]⟩,⟨12,[(0,1),(4,1),(3,18)]⟩,⟨1,[(6,1)]⟩]) (.leaf 25 [⟨1,[(6,1)]⟩,⟨12,[(0,1),(4,1),(3,18)]⟩,⟨2,[(0,1),(1,11)]⟩,⟨2,[(0,1),(1,15)]⟩]))) (.split (1,-1,0) (.split (1,1,12) (.leaf 4 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(1,1),(2,1)]⟩,⟨5,[(0,1),(5,3),(3,18)]⟩]) (.leaf 0 [⟨1,[(1,2),(2,1),(3,6)]⟩,⟨3,[(2,1),(6,2),(3,6)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩])) (.leaf 3 [⟨1,[(4,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨1,[(1,2),(5,1)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot132_checked : checkTree [(-13,-2,-18),(1,0,6),(-1,2,18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot132 = true := by decide

def target1BackwardRoot133 : CoverTree := .leaf 55 [⟨3,[(1,8),(2,1),(3,6)]⟩,⟨3,[(1,2),(2,1),(3,6)]⟩,⟨1,[(0,3),(2,2)]⟩,⟨1,[(0,7),(2,4)]⟩]
theorem target1BackwardRoot133_checked : checkTree [(2,3,132),(0,1,54),(-3,-5,-222),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot133 = true := by decide

def target1BackwardRoot134 : CoverTree := .split (1,-1,-72) (.leaf 54 [⟨1,[(0,2),(1,1),(3,12)]⟩,⟨1,[(0,4),(1,3)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 55 [⟨1,[(4,1)]⟩,⟨1,[(0,1),(1,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(0,1),(2,2),(3,12)]⟩])
theorem target1BackwardRoot134_checked : checkTree [(2,3,132),(-3,-4,-168),(0,-1,-54),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot134 = true := by decide

def target1BackwardRoot135 : CoverTree := .split (1,-1,-72) (.leaf 54 [⟨1,[(0,2),(2,1),(3,12)]⟩,⟨1,[(0,4),(2,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 55 [⟨1,[(4,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨3,[(1,5),(2,2),(3,42)]⟩])
theorem target1BackwardRoot135_checked : checkTree [(-1,-1,-36),(0,-1,-54),(3,4,168),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot135 = true := by decide

theorem targetMeshFamily1Chunk16_covered : FamilyCover targetMeshFamily1Chunk16 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk16,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot128,target1BackwardRoot128_checked⟩
  · exact ⟨target1BackwardRoot129,target1BackwardRoot129_checked⟩
  · exact ⟨target1BackwardRoot130,target1BackwardRoot130_checked⟩
  · exact ⟨target1BackwardRoot131,target1BackwardRoot131_checked⟩
  · exact ⟨target1BackwardRoot132,target1BackwardRoot132_checked⟩
  · exact ⟨target1BackwardRoot133,target1BackwardRoot133_checked⟩
  · exact ⟨target1BackwardRoot134,target1BackwardRoot134_checked⟩
  · exact ⟨target1BackwardRoot135,target1BackwardRoot135_checked⟩

def target1BackwardRoot136 : CoverTree := .leaf 55 [⟨1,[(0,1),(2,3)]⟩,⟨1,[(0,1),(2,1)]⟩,⟨2,[(0,3),(1,1),(3,6)]⟩,⟨2,[(0,5),(1,3),(3,18)]⟩]
theorem target1BackwardRoot136_checked : checkTree [(-1,-2,-90),(3,4,168),(0,1,54),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot136 = true := by decide

def target1BackwardRoot137 : CoverTree := .leaf 55 [⟨3,[(1,7),(2,8),(3,6)]⟩,⟨3,[(1,1),(2,2),(3,6)]⟩,⟨1,[(0,3),(1,1)]⟩,⟨1,[(0,7),(1,3)]⟩]
theorem target1BackwardRoot137_checked : checkTree [(-1,-2,-90),(3,5,222),(-3,-4,-168),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot137 = true := by decide

def target1BackwardRoot138 : CoverTree := .split (1,-1,0) (.split (0,1,12) (.split (-2,-1,0) (.leaf 4 [⟨1,[(4,1)]⟩,⟨5,[(1,1),(5,3),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (-1,-2,0) (.leaf 5 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨4,[(1,1),(2,1),(3,24)]⟩,⟨1,[(7,1)]⟩]) (.leaf 2 [⟨1,[(7,1)]⟩,⟨4,[(1,1),(2,1),(3,24)]⟩,⟨11,[(2,2),(4,7),(3,120)]⟩,⟨1,[(4,1)]⟩]))) (.split (1,2,36) (.leaf 7 [⟨9,[(2,2),(5,5),(3,48)]⟩,⟨1,[(5,1)]⟩,⟨5,[(1,1),(5,2),(3,6)]⟩,⟨1,[(6,1)]⟩]) (.leaf 43 [⟨1,[(6,1)]⟩,⟨4,[(1,1),(6,1),(3,18)]⟩,⟨8,[(1,7),(2,3),(3,48)]⟩,⟨8,[(1,11),(2,7),(3,48)]⟩]))) (.split (0,-1,12) (.split (2,1,0) (.leaf 30 [⟨1,[(4,1)]⟩,⟨9,[(2,1),(5,7),(3,18)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (1,2,0) (.leaf 31 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨4,[(0,1),(2,1),(3,24)]⟩,⟨1,[(7,1)]⟩]) (.leaf 3 [⟨1,[(7,1)]⟩,⟨4,[(0,1),(2,1),(3,24)]⟩,⟨7,[(1,2),(4,3),(3,48)]⟩,⟨1,[(4,1)]⟩]))) (.split (-1,-2,36) (.leaf 24 [⟨13,[(0,2),(5,9),(3,72)]⟩,⟨1,[(5,1)]⟩,⟨9,[(2,1),(5,2),(3,18)]⟩,⟨1,[(6,1)]⟩]) (.leaf 25 [⟨1,[(6,1)]⟩,⟨8,[(2,1),(6,1),(3,30)]⟩,⟨8,[(0,7),(2,11)]⟩,⟨8,[(0,11),(2,15)]⟩])))
theorem target1BackwardRoot138_checked : checkTree [(13,2,18),(5,2,18),(-9,-2,6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot138 = true := by decide

def target1BackwardRoot139 : CoverTree := .split (1,1,24) (.split (-1,-2,-36) (.leaf 43 [⟨1,[(5,1)]⟩,⟨8,[(0,1),(2,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(1,2),(4,1)]⟩]) (.split (0,-1,-12) (.leaf 7 [⟨1,[(1,2),(6,1)]⟩,⟨1,[(6,1)]⟩,⟨8,[(0,1),(2,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 4 [⟨16,[(0,7),(2,15),(3,144)]⟩,⟨13,[(0,1),(6,11),(3,6)]⟩,⟨1,[(6,1)]⟩,⟨16,[(0,1),(2,9),(3,144)]⟩]))) (.split (1,-1,-36) (.split (1,2,72) (.leaf 50 [⟨1,[(6,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 53 [⟨2,[(0,1),(1,9)]⟩,⟨2,[(0,1),(1,13)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨1,[(6,1)]⟩])) (.leaf 40 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨11,[(0,1),(4,13),(3,30)]⟩,⟨2,[(0,1),(1,9)]⟩]))
theorem target1BackwardRoot139_checked : checkTree [(13,2,18),(-1,0,6),(-5,-2,-18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot139 = true := by decide

def target1BackwardRoot140 : CoverTree := .split (-1,-2,-72) (.split (0,1,48) (.leaf 53 [⟨1,[(2,2),(5,1)]⟩,⟨1,[(5,1)]⟩,⟨8,[(0,1),(1,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 55 [⟨16,[(0,11),(1,3),(3,144)]⟩,⟨9,[(1,1),(5,7),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,2),(5,3)]⟩])) (.split (-1,-1,-24) (.leaf 50 [⟨1,[(4,1)]⟩,⟨8,[(0,1),(1,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(2,2),(5,1)]⟩]) (.split (-1,1,36) (.leaf 43 [⟨1,[(1,1),(2,8),(3,6)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 44 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨7,[(1,1),(5,9),(3,30)]⟩,⟨2,[(1,1),(2,5),(3,24)]⟩])))
theorem target1BackwardRoot140_checked : checkTree [(1,2,90),(-9,-2,6),(1,0,-6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot140 = true := by decide

def target1BackwardRoot141 : CoverTree := .split (1,0,-12) (.split (1,1,36) (.split (-1,-2,-72) (.leaf 57 [⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨3,[(1,2),(5,7)]⟩]) (.leaf 56 [⟨2,[(1,1),(4,1),(3,30)]⟩,⟨2,[(1,1),(4,5),(3,6)]⟩,⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 55 [⟨1,[(0,2),(5,3)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1),(5,1)]⟩,⟨2,[(0,1),(4,3),(3,18)]⟩])) (.split (1,2,72) (.split (-1,-1,-24) (.leaf 50 [⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(6,1)]⟩,⟨7,[(2,2),(6,11),(3,24)]⟩]) (.split (1,-1,-36) (.leaf 44 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1),(6,1)]⟩,⟨1,[(4,3),(7,1)]⟩]) (.leaf 43 [⟨1,[(1,2),(2,1),(3,6)]⟩,⟨4,[(1,1),(2,1),(3,24)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩]))) (.split (0,1,48) (.leaf 53 [⟨2,[(2,1),(4,5),(3,18)]⟩,⟨1,[(6,1)]⟩,⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 55 [⟨2,[(0,1),(4,3),(3,18)]⟩,⟨1,[(4,1),(6,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,2),(6,3)]⟩])))
theorem target1BackwardRoot141_checked : checkTree [(1,2,90),(-5,-2,-18),(9,2,-6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot141 = true := by decide

def target1BackwardRoot142 : CoverTree := .split (1,-1,-36) (.split (-1,-1,-24) (.split (1,2,72) (.split (1,0,-12) (.leaf 56 [⟨1,[(5,3),(6,1)]⟩,⟨1,[(5,1),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 50 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(4,1)]⟩])) (.leaf 57 [⟨1,[(6,1)]⟩,⟨4,[(2,1),(6,1),(3,6)]⟩,⟨4,[(0,3),(2,5)]⟩,⟨4,[(0,7),(2,9)]⟩])) (.split (0,1,36) (.leaf 44 [⟨1,[(4,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(0,1),(1,3)]⟩]) (.leaf 56 [⟨2,[(0,1),(1,3)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1),(6,1)]⟩,⟨5,[(0,1),(5,12),(3,54)]⟩]))) (.split (-1,-2,-36) (.leaf 43 [⟨1,[(5,1)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨1,[(1,2),(4,1)]⟩,⟨1,[(4,1)]⟩]) (.leaf 7 [⟨2,[(0,1),(1,3)]⟩,⟨2,[(0,1),(1,7)]⟩,⟨1,[(1,1),(3,6)]⟩,⟨1,[(5,1)]⟩]))
theorem target1BackwardRoot142_checked : checkTree [(-7,-2,18),(1,0,-6),(5,2,18),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot142 = true := by decide

def target1BackwardRoot143 : CoverTree := .split (-1,-2,0) (.split (0,1,12) (.split (2,1,0) (.leaf 5 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(4,1)]⟩]) (.leaf 4 [⟨5,[(1,3),(6,11),(3,18)]⟩,⟨9,[(1,1),(5,7),(3,30)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩])) (.split (1,2,36) (.leaf 7 [⟨1,[(2,2),(5,1)]⟩,⟨1,[(5,1)]⟩,⟨8,[(1,1),(4,1),(3,6)]⟩,⟨1,[(6,1)]⟩]) (.leaf 43 [⟨1,[(6,1)]⟩,⟨8,[(1,1),(4,1),(3,6)]⟩,⟨2,[(1,1),(2,7),(3,12)]⟩,⟨2,[(1,1),(2,11),(3,12)]⟩]))) (.split (0,-1,12) (.split (-1,1,0) (.leaf 30 [⟨1,[(6,1)]⟩,⟨7,[(0,1),(5,5),(3,6)]⟩,⟨1,[(5,1)]⟩,⟨11,[(1,3),(6,5),(3,18)]⟩]) (.leaf 2 [⟨1,[(4,1)]⟩,⟨1,[(2,1),(3,6)]⟩,⟨1,[(2,2),(6,1)]⟩,⟨1,[(6,1)]⟩])) (.split (-1,-2,36) (.leaf 24 [⟨9,[(1,2),(5,5),(3,72)]⟩,⟨1,[(5,1)]⟩,⟨7,[(0,1),(5,2),(3,6)]⟩,⟨1,[(6,1)]⟩]) (.leaf 25 [⟨1,[(6,1)]⟩,⟨6,[(0,1),(6,1),(3,18)]⟩,⟨4,[(0,7),(1,5)]⟩,⟨4,[(0,11),(1,9)]⟩])))
theorem target1BackwardRoot143_checked : checkTree [(-7,-2,18),(9,2,-6),(-1,0,6),(0,0,1)] (familyFacets targetKiteFamily1) target1BackwardRoot143 = true := by decide

theorem targetMeshFamily1Chunk17_covered : FamilyCover targetMeshFamily1Chunk17 targetKiteFamily1 := by
  intro p hp
  simp only [targetMeshFamily1Chunk17,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1BackwardRoot136,target1BackwardRoot136_checked⟩
  · exact ⟨target1BackwardRoot137,target1BackwardRoot137_checked⟩
  · exact ⟨target1BackwardRoot138,target1BackwardRoot138_checked⟩
  · exact ⟨target1BackwardRoot139,target1BackwardRoot139_checked⟩
  · exact ⟨target1BackwardRoot140,target1BackwardRoot140_checked⟩
  · exact ⟨target1BackwardRoot141,target1BackwardRoot141_checked⟩
  · exact ⟨target1BackwardRoot142,target1BackwardRoot142_checked⟩
  · exact ⟨target1BackwardRoot143,target1BackwardRoot143_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
