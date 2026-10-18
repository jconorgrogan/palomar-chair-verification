module

public import SpectreGeometry.ReverseClusterTriangulationTarget01Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target1ForwardRoot48 : CoverTree := .split (13,9,-114) (.split (13,8,-162) (.split (-13,-7,210) (.leaf 161 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,3),(7,1),(4,6)]⟩]) (.split (-13,-10,144) (.leaf 162 [⟨1,[(0,13),(7,2)]⟩,⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 163 [⟨2,[(0,13),(1,5),(4,36)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩]))) (.leaf 158 [⟨1,[(6,1)]⟩,⟨1,[(1,3),(5,1),(4,6)]⟩,⟨1,[(5,1)]⟩])) (.split (-13,-6,180) (.split (13,7,-132) (.leaf 156 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 153 [⟨1,[(7,1)]⟩,⟨2,[(2,23),(3,3),(4,108)]⟩,⟨2,[(2,17),(3,9),(4,12)]⟩])) (.leaf 157 [⟨3,[(0,1),(3,2),(4,36)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]))
theorem target1ForwardRoot48_checked : checkTree [(-2,-1,36),(0,-1,-24),(1,0,-24),(1,2,36),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot48 = true := by decide

def target1ForwardRoot49 : CoverTree := .split (-13,-7,132) (.split (-13,-9,36) (.split (13,6,-102) (.leaf 152 [⟨1,[(1,1),(3,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 151 [⟨1,[(1,1),(3,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,10),(2,3),(4,36)]⟩])) (.leaf 153 [⟨1,[(5,1)]⟩,⟨1,[(1,10),(2,3),(4,36)]⟩,⟨1,[(6,1)]⟩])) (.split (13,6,-180) (.split (-13,-9,114) (.leaf 157 [⟨1,[(1,1),(3,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.split (-13,-8,162) (.leaf 158 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩]) (.split (-13,-7,210) (.leaf 161 [⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩,⟨3,[(0,23),(3,16),(4,108)]⟩]) (.leaf 162 [⟨1,[(1,1),(3,1)]⟩,⟨3,[(0,23),(3,16),(4,108)]⟩,⟨1,[(9,1)]⟩])))) (.leaf 156 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(1,13),(6,3)]⟩]))
theorem target1ForwardRoot49_checked : checkTree [(-1,-2,-36),(1,0,-24),(1,1,12),(-1,1,72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot49 = true := by decide

def target1ForwardRoot50 : CoverTree := .split (1,0,-6) (.split (9,2,-6) (.split (-5,-2,-18) (.leaf 141 [⟨1,[(0,1),(4,18)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 142 [⟨1,[(1,5),(2,2),(4,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩])) (.leaf 140 [⟨1,[(0,1),(4,18)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩])) (.split (13,2,18) (.leaf 139 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(2,2),(5,3),(4,12)]⟩]) (.split (3,1,30) (.leaf 131 [⟨1,[(6,1)]⟩,⟨1,[(1,1),(3,2),(4,42)]⟩,⟨1,[(7,1)]⟩]) (.leaf 130 [⟨1,[(0,3),(3,2),(4,18)]⟩,⟨1,[(7,1)]⟩,⟨3,[(0,1),(3,2),(4,18)]⟩])))
theorem target1ForwardRoot50_checked : checkTree [(1,2,72),(-1,0,12),(-1,-1,-24),(1,-1,-36),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot50 = true := by decide

def target1ForwardRoot51 : CoverTree := .split (-5,-3,-144) (.split (2,1,54) (.split (-3,-1,-60) (.split (3,2,96) (.split (9,5,252) (.leaf 58 [⟨1,[(5,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 54 [⟨1,[(6,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩])) (.leaf 55 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩])) (.split (-3,-2,-96) (.leaf 56 [⟨1,[(2,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 57 [⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩]))) (.split (-5,-3,-156) (.leaf 51 [⟨1,[(2,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,1)]⟩]) (.leaf 52 [⟨1,[(6,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(7,1)]⟩]))) (.split (-5,-2,-96) (.split (1,1,42) (.split (-10,-7,-306) (.leaf 59 [⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 63 [⟨4,[(0,5),(6,3)]⟩,⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 60 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩])) (.split (5,4,162) (.leaf 130 [⟨1,[(7,1)]⟩,⟨3,[(0,4),(3,5),(4,18)]⟩,⟨3,[(0,2),(7,1)]⟩]) (.split (1,1,42) (.leaf 62 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 61 [⟨1,[(1,1),(3,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩]))))
theorem target1ForwardRoot51_checked : checkTree [(-1,-2,-72),(1,0,12),(1,1,48),(-1,1,36),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot51 = true := by decide

def target1ForwardRoot52 : CoverTree := .split (-1,-1,-42) (.split (5,2,96) (.leaf 61 [⟨1,[(2,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (3,2,96) (.split (5,3,144) (.leaf 60 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 57 [⟨1,[(8,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(7,1)]⟩])) (.leaf 56 [⟨1,[(1,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(0,1),(1,2)]⟩]))) (.split (5,4,162) (.leaf 130 [⟨1,[(6,1)]⟩,⟨1,[(3,2),(5,1)]⟩,⟨2,[(0,1),(1,1)]⟩]) (.leaf 62 [⟨1,[(6,1)]⟩,⟨2,[(0,3),(5,7),(4,6)]⟩,⟨1,[(5,1)]⟩]))
theorem target1ForwardRoot52_checked : checkTree [(1,-1,-36),(1,1,48),(0,1,48),(-2,-1,-36),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot52 = true := by decide

def target1ForwardRoot53 : CoverTree := .split (1,0,-6) (.split (-9,-2,6) (.leaf 140 [⟨1,[(1,2),(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 141 [⟨1,[(1,2),(5,1)]⟩,⟨1,[(2,4),(3,1),(4,6)]⟩,⟨1,[(6,1)]⟩])) (.split (3,1,30) (.split (-13,-2,-18) (.leaf 131 [⟨1,[(7,1)]⟩,⟨3,[(0,4),(3,5),(4,162)]⟩,⟨1,[(6,1)]⟩]) (.leaf 139 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(2,4),(3,1),(4,6)]⟩])) (.leaf 130 [⟨1,[(0,4),(5,3)]⟩,⟨1,[(6,1)]⟩,⟨3,[(0,2),(3,1),(4,18)]⟩]))
theorem target1ForwardRoot53_checked : checkTree [(2,1,36),(0,1,48),(-1,0,12),(-1,-2,-72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot53 = true := by decide

def target1ForwardRoot54 : CoverTree := .split (4,3,102) (.split (-1,-3,-156) (.leaf 15 [⟨1,[(1,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.split (-2,-3,-132) (.leaf 16 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (3,4,168) (.leaf 135 [⟨1,[(2,1)]⟩,⟨2,[(2,1),(3,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 134 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨2,[(2,1),(3,1)]⟩])))) (.split (4,5,234) (.split (1,1,42) (.split (-1,-3,-156) (.leaf 14 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩]) (.split (-5,-6,-258) (.leaf 13 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩]) (.leaf 17 [⟨7,[(3,6),(5,5),(4,18)]⟩,⟨1,[(9,1)]⟩,⟨1,[(5,1)]⟩]))) (.leaf 11 [⟨1,[(7,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 10 [⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(3,1)]⟩]))
theorem target1ForwardRoot54_checked : checkTree [(1,2,108),(-1,0,24),(-1,-1,-36),(1,-1,-72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot54 = true := by decide

def target1ForwardRoot55 : CoverTree := .split (5,6,258) (.split (3,4,168) (.split (9,2,-6) (.split (1,2,90) (.leaf 141 [⟨1,[(8,1)]⟩,⟨1,[(1,8),(8,3)]⟩,⟨1,[(7,1)]⟩]) (.split (0,1,54) (.leaf 136 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(9,1)]⟩]) (.leaf 135 [⟨1,[(1,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(6,1)]⟩]))) (.leaf 140 [⟨15,[(6,8),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨2,[(2,1),(3,1)]⟩])) (.split (2,3,132) (.split (3,5,222) (.split (1,2,90) (.leaf 140 [⟨1,[(9,1)]⟩,⟨1,[(6,8),(9,15)]⟩,⟨1,[(2,2),(9,1)]⟩]) (.leaf 137 [⟨1,[(9,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩])) (.split (0,1,54) (.leaf 133 [⟨1,[(7,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 134 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(9,1)]⟩]))) (.split (-4,-3,-102) (.leaf 17 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 16 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨7,[(0,9),(8,4),(4,36)]⟩])))) (.split (-5,-4,-162) (.leaf 9 [⟨1,[(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩]) (.split (-1,-1,-42) (.leaf 12 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,1)]⟩]) (.leaf 13 [⟨1,[(7,1)]⟩,⟨1,[(0,1),(7,2)]⟩,⟨1,[(5,1)]⟩])))
theorem target1ForwardRoot55_checked : checkTree [(-1,1,72),(-1,-1,-36),(0,-1,-48),(2,1,36),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot55 = true := by decide

theorem targetKiteFamily1Chunk6_covered : FamilyCover targetKiteFamily1Chunk6 targetMeshFamily1 := by
  intro p hp
  simp only [targetKiteFamily1Chunk6,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1ForwardRoot48,target1ForwardRoot48_checked⟩
  · exact ⟨target1ForwardRoot49,target1ForwardRoot49_checked⟩
  · exact ⟨target1ForwardRoot50,target1ForwardRoot50_checked⟩
  · exact ⟨target1ForwardRoot51,target1ForwardRoot51_checked⟩
  · exact ⟨target1ForwardRoot52,target1ForwardRoot52_checked⟩
  · exact ⟨target1ForwardRoot53,target1ForwardRoot53_checked⟩
  · exact ⟨target1ForwardRoot54,target1ForwardRoot54_checked⟩
  · exact ⟨target1ForwardRoot55,target1ForwardRoot55_checked⟩

def target1ForwardRoot56 : CoverTree := .split (5,1,-36) (.leaf 146 [⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(5,1)]⟩]) (.split (-7,-2,18) (.split (5,2,18) (.leaf 142 [⟨1,[(6,1)]⟩,⟨1,[(2,1),(4,6)]⟩,⟨1,[(7,1)]⟩]) (.leaf 141 [⟨1,[(3,1),(4,18)]⟩,⟨1,[(7,1)]⟩,⟨1,[(2,8),(3,1),(4,18)]⟩])) (.leaf 145 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1)]⟩]))
theorem target1ForwardRoot56_checked : checkTree [(-2,-1,0),(0,-1,-36),(1,0,-12),(1,2,72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot56 = true := by decide

def target1ForwardRoot57 : CoverTree := .split (-5,-1,36) (.split (-5,-2,-18) (.leaf 141 [⟨2,[(2,3),(3,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(1,7),(2,2),(4,6)]⟩]) (.split (-7,-2,18) (.leaf 142 [⟨1,[(7,1)]⟩,⟨1,[(1,1),(4,6)]⟩,⟨1,[(6,1)]⟩]) (.leaf 145 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1),(3,1)]⟩]))) (.leaf 146 [⟨1,[(3,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(5,1)]⟩])
theorem target1ForwardRoot57_checked : checkTree [(-1,-2,-72),(1,0,-12),(1,1,36),(-1,1,72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot57 = true := by decide

def target1ForwardRoot58 : CoverTree := .split (14,9,-240) (.split (-4,-3,66) (.split (-11,-9,150) (.leaf 167 [⟨1,[(0,1),(2,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 168 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩])) (.leaf 171 [⟨1,[(6,1)]⟩,⟨2,[(0,1),(1,3)]⟩,⟨1,[(0,4),(2,15),(4,90)]⟩])) (.split (13,10,-144) (.split (-13,-9,192) (.leaf 163 [⟨1,[(7,1)]⟩,⟨1,[(2,3),(6,1),(4,6)]⟩,⟨1,[(6,1)]⟩]) (.leaf 166 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨14,[(2,27),(5,11),(4,108)]⟩])) (.leaf 162 [⟨3,[(0,2),(3,1),(4,36)]⟩,⟨1,[(6,1)]⟩,⟨3,[(0,1),(3,20),(4,18)]⟩]))
theorem target1ForwardRoot58_checked : checkTree [(-1,1,72),(-1,-1,12),(0,-1,-24),(2,1,-36),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot58 = true := by decide

def target1ForwardRoot59 : CoverTree := .split (13,6,-180) (.split (-13,-9,114) (.leaf 157 [⟨1,[(2,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.split (13,8,-162) (.split (-13,-7,210) (.leaf 161 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨3,[(0,7),(3,23),(4,108)]⟩]) (.leaf 162 [⟨1,[(2,1)]⟩,⟨3,[(0,7),(3,23),(4,108)]⟩,⟨1,[(8,1)]⟩])) (.leaf 158 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]))) (.split (13,9,-36) (.split (-13,-7,132) (.leaf 153 [⟨1,[(7,1)]⟩,⟨1,[(0,5),(1,8),(4,96)]⟩,⟨1,[(6,1)]⟩]) (.leaf 156 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨19,[(0,39),(5,22),(4,1014)]⟩])) (.leaf 152 [⟨1,[(2,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(0,7),(1,19),(4,72)]⟩]))
theorem target1ForwardRoot59_checked : checkTree [(1,-1,-72),(1,1,12),(0,1,48),(-2,-1,36),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot59 = true := by decide

def target1ForwardRoot60 : CoverTree := .split (-13,-10,144) (.leaf 162 [⟨1,[(1,1)]⟩,⟨1,[(5,1)]⟩,⟨2,[(0,13),(1,1)]⟩]) (.split (14,9,-240) (.leaf 167 [⟨1,[(2,1)]⟩,⟨2,[(2,13),(3,9)]⟩,⟨1,[(6,1)]⟩]) (.split (-13,-9,192) (.leaf 163 [⟨1,[(7,1)]⟩,⟨2,[(0,13),(1,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 166 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(2,13),(3,9)]⟩])))
theorem target1ForwardRoot60_checked : checkTree [(2,1,-36),(0,1,48),(-1,0,48),(-1,-2,-36),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot60 = true := by decide

def target1ForwardRoot61 : CoverTree := .split (11,9,-150) (.split (-2,-1,54) (.split (4,3,-66) (.leaf 171 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(1,15),(3,11),(4,90)]⟩]) (.leaf 168 [⟨1,[(7,1)]⟩,⟨20,[(3,27),(5,23),(4,594)]⟩,⟨1,[(5,1)]⟩])) (.leaf 172 [⟨1,[(1,6),(6,1)]⟩,⟨1,[(0,1),(2,21),(4,162)]⟩,⟨1,[(6,1)]⟩])) (.split (14,9,-240) (.leaf 167 [⟨1,[(1,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (13,10,-144) (.split (-13,-9,192) (.leaf 163 [⟨1,[(8,1)]⟩,⟨3,[(0,20),(3,19),(4,18)]⟩,⟨1,[(7,1)]⟩]) (.leaf 166 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩])) (.leaf 162 [⟨1,[(0,1),(2,1)]⟩,⟨1,[(7,1)]⟩,⟨3,[(0,20),(3,19),(4,18)]⟩])))
theorem target1ForwardRoot61_checked : checkTree [(1,2,36),(-1,0,48),(-1,-1,12),(1,-1,-72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot61 = true := by decide

def target1ForwardRoot62 : CoverTree := .split (1,4,102) (.split (2,-1,-156) (.leaf 24 [⟨1,[(1,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.split (1,-2,-132) (.leaf 25 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (3,-2,-240) (.leaf 69 [⟨1,[(7,1)]⟩,⟨1,[(2,1)]⟩,⟨1,[(8,1)]⟩]) (.split (-3,4,312) (.leaf 72 [⟨2,[(2,3),(3,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(2,1)]⟩]) (.leaf 68 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩]))))) (.split (-1,4,234) (.split (0,1,42) (.split (2,-1,-156) (.leaf 23 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩]) (.split (1,-5,-258) (.leaf 22 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩]) (.leaf 26 [⟨7,[(3,6),(5,5),(4,18)]⟩,⟨1,[(9,1)]⟩,⟨1,[(5,1)]⟩]))) (.leaf 20 [⟨1,[(7,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 19 [⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(3,1)]⟩]))
theorem target1ForwardRoot62_checked : checkTree [(-1,1,108),(-1,-1,24),(0,-1,-36),(2,1,-72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot62 = true := by decide

def target1ForwardRoot63 : CoverTree := .split (-1,5,258) (.split (1,-1,-90) (.split (-1,2,132) (.split (3,-4,-312) (.split (-3,2,240) (.leaf 68 [⟨1,[(7,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 69 [⟨1,[(7,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(9,1)]⟩])) (.leaf 72 [⟨1,[(6,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(1,1)]⟩])) (.split (-1,-4,-102) (.leaf 26 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 25 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨7,[(0,9),(8,4),(4,36)]⟩]))) (.split (7,-3,-462) (.split (3,-2,-228) (.split (5,-4,-408) (.leaf 73 [⟨1,[(6,1)]⟩,⟨1,[(1,1),(6,2)]⟩,⟨1,[(9,1)]⟩]) (.leaf 77 [⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(1,2),(2,1)]⟩])) (.leaf 78 [⟨1,[(8,1)]⟩,⟨1,[(1,1),(6,1)]⟩,⟨1,[(7,1)]⟩])) (.split (-4,1,234) (.leaf 172 [⟨1,[(8,1)]⟩,⟨1,[(0,10),(1,9),(4,54)]⟩,⟨1,[(2,3),(6,1)]⟩]) (.leaf 82 [⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,3),(2,2),(4,12)]⟩])))) (.split (-1,-5,-162) (.leaf 18 [⟨1,[(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩]) (.split (0,-1,-42) (.leaf 21 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,1)]⟩]) (.leaf 22 [⟨1,[(7,1)]⟩,⟨1,[(0,1),(7,2)]⟩,⟨1,[(5,1)]⟩])))
theorem target1ForwardRoot63_checked : checkTree [(-2,-1,72),(0,-1,-36),(1,0,-48),(1,2,36),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot63 = true := by decide

theorem targetKiteFamily1Chunk7_covered : FamilyCover targetKiteFamily1Chunk7 targetMeshFamily1 := by
  intro p hp
  simp only [targetKiteFamily1Chunk7,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1ForwardRoot56,target1ForwardRoot56_checked⟩
  · exact ⟨target1ForwardRoot57,target1ForwardRoot57_checked⟩
  · exact ⟨target1ForwardRoot58,target1ForwardRoot58_checked⟩
  · exact ⟨target1ForwardRoot59,target1ForwardRoot59_checked⟩
  · exact ⟨target1ForwardRoot60,target1ForwardRoot60_checked⟩
  · exact ⟨target1ForwardRoot61,target1ForwardRoot61_checked⟩
  · exact ⟨target1ForwardRoot62,target1ForwardRoot62_checked⟩
  · exact ⟨target1ForwardRoot63,target1ForwardRoot63_checked⟩

def target1ForwardRoot64 : CoverTree := .split (2,1,-54) (.split (-20,-19,450) (.leaf 172 [⟨1,[(0,1),(3,3),(4,18)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 173 [⟨1,[(0,1),(3,3),(4,18)]⟩,⟨1,[(0,7),(2,3),(4,54)]⟩,⟨1,[(6,1)]⟩])) (.leaf 171 [⟨1,[(1,1),(2,3),(4,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,7),(2,3),(4,54)]⟩])
theorem target1ForwardRoot64_checked : checkTree [(-1,-2,0),(1,0,-36),(1,1,-12),(-1,1,72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot64 = true := by decide

def target1ForwardRoot65 : CoverTree := .split (-4,1,234) (.split (-20,-19,450) (.leaf 172 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(0,1),(1,3)]⟩]) (.leaf 173 [⟨1,[(5,1)]⟩,⟨1,[(0,6),(3,5),(4,90)]⟩,⟨1,[(6,1)]⟩])) (.split (7,-3,-462) (.split (-3,2,228) (.leaf 78 [⟨1,[(7,1)]⟩,⟨2,[(2,1),(3,1)]⟩,⟨1,[(6,1)]⟩]) (.split (-5,4,408) (.leaf 77 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨7,[(3,4),(7,5),(4,12)]⟩]) (.leaf 73 [⟨2,[(2,3),(3,1)]⟩,⟨1,[(2,2),(3,1)]⟩,⟨1,[(8,1)]⟩]))) (.leaf 82 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨3,[(3,5),(5,4)]⟩]))
theorem target1ForwardRoot65_checked : checkTree [(1,-1,-72),(1,1,-12),(0,1,36),(-2,-1,72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot65 = true := by decide

def target1ForwardRoot66 : CoverTree := .split (20,19,-450) (.split (-4,-11,18) (.leaf 173 [⟨1,[(0,3),(3,2),(4,18)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 174 [⟨1,[(0,2),(1,3),(4,18)]⟩,⟨2,[(1,9),(6,1),(4,18)]⟩,⟨1,[(6,1)]⟩])) (.leaf 172 [⟨1,[(0,3),(3,2),(4,18)]⟩,⟨1,[(5,1)]⟩,⟨2,[(2,3),(3,1)]⟩])
theorem target1ForwardRoot66_checked : checkTree [(-2,-1,72),(0,-1,-12),(1,0,-36),(1,2,0),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot66 = true := by decide

def target1ForwardRoot67 : CoverTree := .split (3,-2,-228) (.split (-1,1,90) (.split (1,-2,-120) (.split (-2,1,144) (.split (-5,4,408) (.leaf 77 [⟨1,[(5,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 73 [⟨1,[(6,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩])) (.leaf 74 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩])) (.split (2,-1,-144) (.leaf 75 [⟨1,[(2,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 76 [⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩]))) (.split (3,-2,-240) (.leaf 70 [⟨1,[(2,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,1)]⟩]) (.leaf 71 [⟨1,[(6,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(7,1)]⟩]))) (.split (2,-3,-192) (.split (1,0,-54) (.leaf 79 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩]) (.split (7,-3,-462) (.leaf 78 [⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 82 [⟨4,[(0,5),(6,3)]⟩,⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩]))) (.split (-4,1,234) (.leaf 173 [⟨1,[(7,1)]⟩,⟨1,[(0,1),(3,6),(4,90)]⟩,⟨1,[(0,16),(7,3)]⟩]) (.split (-1,0,54) (.leaf 81 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 80 [⟨1,[(1,1),(3,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩]))))
theorem target1ForwardRoot67_checked : checkTree [(2,1,-72),(0,1,36),(-1,0,60),(-1,-2,0),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot67 = true := by decide

def target1ForwardRoot68 : CoverTree := .split (1,0,-54) (.split (-2,3,192) (.leaf 80 [⟨1,[(2,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (-2,1,144) (.split (-3,2,228) (.leaf 79 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 76 [⟨1,[(8,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(7,1)]⟩])) (.leaf 75 [⟨1,[(1,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(0,1),(1,2)]⟩]))) (.split (-4,1,234) (.leaf 173 [⟨1,[(6,1)]⟩,⟨1,[(3,11),(5,15)]⟩,⟨1,[(0,13),(3,7),(4,54)]⟩]) (.leaf 81 [⟨1,[(6,1)]⟩,⟨2,[(0,3),(5,7),(4,6)]⟩,⟨1,[(5,1)]⟩]))
theorem target1ForwardRoot68_checked : checkTree [(1,2,0),(-1,0,60),(-1,-1,36),(1,-1,-72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot68 = true := by decide

def target1ForwardRoot69 : CoverTree := .split (-4,-11,18) (.leaf 173 [⟨2,[(0,5),(1,3)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,6),(3,13),(4,54)]⟩]) (.split (-4,-5,126) (.leaf 174 [⟨1,[(6,1)]⟩,⟨1,[(3,1),(4,18)]⟩,⟨1,[(5,1)]⟩]) (.split (7,8,-234) (.split (10,11,-342) (.leaf 199 [⟨1,[(1,1)]⟩,⟨1,[(1,11),(2,2),(4,6)]⟩,⟨1,[(8,1)]⟩]) (.leaf 198 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(0,1),(2,3)]⟩])) (.split (-16,-19,522) (.split (9,11,-288) (.leaf 184 [⟨1,[(9,1)]⟩,⟨1,[(8,1)]⟩,⟨4,[(2,1),(6,1),(4,18)]⟩]) (.split (-17,-21,540) (.leaf 178 [⟨1,[(6,1)]⟩,⟨1,[(10,1)]⟩,⟨4,[(2,1),(6,5),(4,18)]⟩]) (.leaf 179 [⟨1,[(9,1)]⟩,⟨1,[(1,7),(2,2)]⟩,⟨1,[(10,1)]⟩]))) (.leaf 185 [⟨1,[(7,1)]⟩,⟨1,[(1,11),(2,3),(4,12)]⟩,⟨1,[(8,1)]⟩]))))
theorem target1ForwardRoot69_checked : checkTree [(-1,1,72),(-1,-1,36),(0,-1,-12),(2,1,-72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot69 = true := by decide

def target1ForwardRoot70 : CoverTree := .split (3,-1,-162) (.split (-5,-1,270) (.split (-1,0,54) (.split (3,2,-144) (.leaf 32 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩]) (.split (6,1,-306) (.leaf 31 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩]) (.leaf 35 [⟨7,[(3,6),(5,5),(4,18)]⟩,⟨1,[(9,1)]⟩,⟨1,[(5,1)]⟩]))) (.leaf 29 [⟨1,[(7,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 28 [⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(3,1)]⟩])) (.split (3,2,-144) (.leaf 33 [⟨1,[(1,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.split (3,1,-144) (.leaf 34 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (-4,-1,192) (.leaf 189 [⟨1,[(2,1)]⟩,⟨2,[(2,1),(3,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 188 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨2,[(2,1),(3,1)]⟩]))))
theorem target1ForwardRoot70_checked : checkTree [(-2,-1,108),(0,-1,0),(1,0,-48),(1,2,-36),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot70 = true := by decide

def target1ForwardRoot71 : CoverTree := .split (-6,-1,306) (.split (-4,-1,192) (.split (4,5,-144) (.split (-2,-1,90) (.leaf 193 [⟨1,[(8,1)]⟩,⟨1,[(1,3),(8,1)]⟩,⟨1,[(7,1)]⟩]) (.split (-1,-1,42) (.leaf 190 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(9,1)]⟩]) (.leaf 189 [⟨1,[(1,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(6,1)]⟩]))) (.split (5,4,-198) (.leaf 192 [⟨8,[(6,3),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 196 [⟨1,[(2,1)]⟩,⟨1,[(8,1)]⟩,⟨2,[(0,1),(1,3)]⟩]))) (.split (-3,-1,144) (.split (-5,-2,234) (.split (2,1,-90) (.leaf 191 [⟨1,[(9,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩]) (.split (5,4,-198) (.leaf 192 [⟨1,[(9,1)]⟩,⟨1,[(6,3),(9,8)]⟩,⟨1,[(10,1)]⟩]) (.leaf 196 [⟨1,[(2,1)]⟩,⟨1,[(10,1)]⟩,⟨1,[(1,3),(9,1)]⟩]))) (.split (-1,-1,42) (.leaf 187 [⟨1,[(7,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 188 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(9,1)]⟩]))) (.split (3,-1,-162) (.leaf 35 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 34 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨7,[(0,9),(8,4),(4,36)]⟩])))) (.split (4,-1,-234) (.leaf 27 [⟨1,[(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩]) (.split (1,0,-54) (.leaf 30 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,1)]⟩]) (.leaf 31 [⟨1,[(7,1)]⟩,⟨1,[(0,1),(7,2)]⟩,⟨1,[(5,1)]⟩])))
theorem target1ForwardRoot71_checked : checkTree [(-1,-2,36),(1,0,-48),(1,1,-36),(-1,1,72),(0,0,1)] (familyFacets targetMeshFamily1) target1ForwardRoot71 = true := by decide

theorem targetKiteFamily1Chunk8_covered : FamilyCover targetKiteFamily1Chunk8 targetMeshFamily1 := by
  intro p hp
  simp only [targetKiteFamily1Chunk8,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target1ForwardRoot64,target1ForwardRoot64_checked⟩
  · exact ⟨target1ForwardRoot65,target1ForwardRoot65_checked⟩
  · exact ⟨target1ForwardRoot66,target1ForwardRoot66_checked⟩
  · exact ⟨target1ForwardRoot67,target1ForwardRoot67_checked⟩
  · exact ⟨target1ForwardRoot68,target1ForwardRoot68_checked⟩
  · exact ⟨target1ForwardRoot69,target1ForwardRoot69_checked⟩
  · exact ⟨target1ForwardRoot70,target1ForwardRoot70_checked⟩
  · exact ⟨target1ForwardRoot71,target1ForwardRoot71_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
