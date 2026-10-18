module

public import SpectreGeometry.ReverseClusterTriangulationTarget00Data

@[expose] public section


namespace SpectreGeometry.ReverseClusterTriangulation
open SpectreClusters HalfplaneCertificate SpectreClusters.BodyBSP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def target0ForwardRoot48 : CoverTree := .split (13,9,-114) (.split (13,8,-162) (.split (-13,-7,210) (.leaf 161 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,3),(7,1),(4,6)]⟩]) (.split (-13,-10,144) (.leaf 162 [⟨1,[(0,13),(7,2)]⟩,⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 163 [⟨2,[(0,13),(1,5),(4,36)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩]))) (.leaf 158 [⟨1,[(6,1)]⟩,⟨1,[(1,3),(5,1),(4,6)]⟩,⟨1,[(5,1)]⟩])) (.split (-13,-6,180) (.split (13,7,-132) (.leaf 156 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 153 [⟨1,[(7,1)]⟩,⟨2,[(2,23),(3,3),(4,108)]⟩,⟨2,[(2,17),(3,9),(4,12)]⟩])) (.leaf 157 [⟨3,[(0,1),(3,2),(4,36)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]))
theorem target0ForwardRoot48_checked : checkTree [(-2,-1,36),(0,-1,-24),(1,0,-24),(1,2,36),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot48 = true := by decide

def target0ForwardRoot49 : CoverTree := .split (-13,-7,132) (.split (-13,-9,36) (.split (13,6,-102) (.leaf 152 [⟨1,[(1,1),(3,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 151 [⟨1,[(1,1),(3,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,10),(2,3),(4,36)]⟩])) (.leaf 153 [⟨1,[(5,1)]⟩,⟨1,[(1,10),(2,3),(4,36)]⟩,⟨1,[(6,1)]⟩])) (.split (13,6,-180) (.split (-13,-9,114) (.leaf 157 [⟨1,[(1,1),(3,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.split (-13,-8,162) (.leaf 158 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩]) (.split (-13,-7,210) (.leaf 161 [⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩,⟨3,[(0,23),(3,16),(4,108)]⟩]) (.leaf 162 [⟨1,[(1,1),(3,1)]⟩,⟨3,[(0,23),(3,16),(4,108)]⟩,⟨1,[(9,1)]⟩])))) (.leaf 156 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(1,13),(6,3)]⟩]))
theorem target0ForwardRoot49_checked : checkTree [(-1,-2,-36),(1,0,-24),(1,1,12),(-1,1,72),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot49 = true := by decide

def target0ForwardRoot50 : CoverTree := .split (1,0,-6) (.split (9,2,-6) (.split (-5,-2,-18) (.leaf 141 [⟨1,[(0,1),(4,18)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 142 [⟨1,[(1,5),(2,2),(4,6)]⟩,⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩])) (.leaf 140 [⟨1,[(0,1),(4,18)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩])) (.split (13,2,18) (.leaf 139 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(2,2),(5,3),(4,12)]⟩]) (.split (3,1,30) (.leaf 131 [⟨1,[(6,1)]⟩,⟨1,[(1,1),(3,2),(4,42)]⟩,⟨1,[(7,1)]⟩]) (.leaf 130 [⟨1,[(0,3),(3,2),(4,18)]⟩,⟨1,[(7,1)]⟩,⟨3,[(0,1),(3,2),(4,18)]⟩])))
theorem target0ForwardRoot50_checked : checkTree [(1,2,72),(-1,0,12),(-1,-1,-24),(1,-1,-36),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot50 = true := by decide

def target0ForwardRoot51 : CoverTree := .split (-5,-3,-144) (.split (2,1,54) (.split (-3,-1,-60) (.split (3,2,96) (.split (9,5,252) (.leaf 62 [⟨1,[(5,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 58 [⟨1,[(6,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩])) (.leaf 59 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩])) (.split (-3,-2,-96) (.leaf 60 [⟨1,[(2,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 61 [⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩]))) (.split (-5,-3,-156) (.leaf 55 [⟨1,[(2,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,1)]⟩]) (.leaf 56 [⟨1,[(6,1)]⟩,⟨1,[(1,1)]⟩,⟨1,[(7,1)]⟩]))) (.split (-5,-2,-96) (.split (1,1,42) (.split (-10,-7,-306) (.leaf 63 [⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 67 [⟨4,[(0,5),(6,3)]⟩,⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 64 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩])) (.split (5,4,162) (.leaf 130 [⟨1,[(7,1)]⟩,⟨3,[(0,4),(3,5),(4,18)]⟩,⟨3,[(0,2),(7,1)]⟩]) (.split (1,1,42) (.leaf 66 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 65 [⟨1,[(1,1),(3,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩]))))
theorem target0ForwardRoot51_checked : checkTree [(-1,-2,-72),(1,0,12),(1,1,48),(-1,1,36),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot51 = true := by decide

def target0ForwardRoot52 : CoverTree := .split (-1,-1,-42) (.split (5,2,96) (.leaf 65 [⟨1,[(2,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (3,2,96) (.split (5,3,144) (.leaf 64 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 61 [⟨1,[(8,1)]⟩,⟨1,[(0,1),(1,2)]⟩,⟨1,[(7,1)]⟩])) (.leaf 60 [⟨1,[(1,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(0,1),(1,2)]⟩]))) (.split (5,4,162) (.leaf 130 [⟨1,[(6,1)]⟩,⟨1,[(3,2),(5,1)]⟩,⟨2,[(0,1),(1,1)]⟩]) (.leaf 66 [⟨1,[(6,1)]⟩,⟨2,[(0,3),(5,7),(4,6)]⟩,⟨1,[(5,1)]⟩]))
theorem target0ForwardRoot52_checked : checkTree [(1,-1,-36),(1,1,48),(0,1,48),(-2,-1,-36),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot52 = true := by decide

def target0ForwardRoot53 : CoverTree := .split (1,0,-6) (.split (-9,-2,6) (.leaf 140 [⟨1,[(1,2),(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 141 [⟨1,[(1,2),(5,1)]⟩,⟨1,[(2,4),(3,1),(4,6)]⟩,⟨1,[(6,1)]⟩])) (.split (3,1,30) (.split (-13,-2,-18) (.leaf 131 [⟨1,[(7,1)]⟩,⟨3,[(0,4),(3,5),(4,162)]⟩,⟨1,[(6,1)]⟩]) (.leaf 139 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(2,4),(3,1),(4,6)]⟩])) (.leaf 130 [⟨1,[(0,4),(5,3)]⟩,⟨1,[(6,1)]⟩,⟨3,[(0,2),(3,1),(4,18)]⟩]))
theorem target0ForwardRoot53_checked : checkTree [(2,1,36),(0,1,48),(-1,0,12),(-1,-2,-72),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot53 = true := by decide

def target0ForwardRoot54 : CoverTree := .split (4,3,102) (.split (-1,-3,-156) (.leaf 15 [⟨1,[(1,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.split (-2,-3,-132) (.leaf 16 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (3,4,168) (.leaf 135 [⟨1,[(2,1)]⟩,⟨2,[(2,1),(3,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 134 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨2,[(2,1),(3,1)]⟩])))) (.split (4,5,234) (.split (1,1,42) (.split (-1,-3,-156) (.leaf 14 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩]) (.split (-5,-6,-258) (.leaf 13 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩]) (.leaf 17 [⟨7,[(3,6),(5,5),(4,18)]⟩,⟨1,[(9,1)]⟩,⟨1,[(5,1)]⟩]))) (.leaf 11 [⟨1,[(7,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 10 [⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(3,1)]⟩]))
theorem target0ForwardRoot54_checked : checkTree [(1,2,108),(-1,0,24),(-1,-1,-36),(1,-1,-72),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot54 = true := by decide

def target0ForwardRoot55 : CoverTree := .split (5,6,258) (.split (3,4,168) (.split (9,2,-6) (.split (1,2,90) (.leaf 141 [⟨1,[(8,1)]⟩,⟨1,[(1,8),(8,3)]⟩,⟨1,[(7,1)]⟩]) (.split (0,1,54) (.leaf 136 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(9,1)]⟩]) (.leaf 135 [⟨1,[(1,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(6,1)]⟩]))) (.leaf 140 [⟨15,[(6,8),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨2,[(2,1),(3,1)]⟩])) (.split (2,3,132) (.split (3,5,222) (.split (1,2,90) (.leaf 140 [⟨1,[(9,1)]⟩,⟨1,[(6,8),(9,15)]⟩,⟨1,[(2,2),(9,1)]⟩]) (.leaf 137 [⟨1,[(9,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩])) (.split (0,1,54) (.leaf 133 [⟨1,[(7,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 134 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(9,1)]⟩]))) (.split (-4,-3,-102) (.leaf 17 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 16 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨7,[(0,9),(8,4),(4,36)]⟩])))) (.split (-5,-4,-162) (.leaf 9 [⟨1,[(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩]) (.split (-1,-1,-42) (.leaf 12 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,1)]⟩]) (.leaf 13 [⟨1,[(7,1)]⟩,⟨1,[(0,1),(7,2)]⟩,⟨1,[(5,1)]⟩])))
theorem target0ForwardRoot55_checked : checkTree [(-1,1,72),(-1,-1,-36),(0,-1,-48),(2,1,36),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot55 = true := by decide

theorem targetKiteFamily0Chunk6_covered : FamilyCover targetKiteFamily0Chunk6 targetMeshFamily0 := by
  intro p hp
  simp only [targetKiteFamily0Chunk6,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0ForwardRoot48,target0ForwardRoot48_checked⟩
  · exact ⟨target0ForwardRoot49,target0ForwardRoot49_checked⟩
  · exact ⟨target0ForwardRoot50,target0ForwardRoot50_checked⟩
  · exact ⟨target0ForwardRoot51,target0ForwardRoot51_checked⟩
  · exact ⟨target0ForwardRoot52,target0ForwardRoot52_checked⟩
  · exact ⟨target0ForwardRoot53,target0ForwardRoot53_checked⟩
  · exact ⟨target0ForwardRoot54,target0ForwardRoot54_checked⟩
  · exact ⟨target0ForwardRoot55,target0ForwardRoot55_checked⟩

def target0ForwardRoot56 : CoverTree := .split (5,1,-36) (.leaf 146 [⟨1,[(0,1),(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(5,1)]⟩]) (.split (-7,-2,18) (.split (5,2,18) (.leaf 142 [⟨1,[(6,1)]⟩,⟨1,[(2,1),(4,6)]⟩,⟨1,[(7,1)]⟩]) (.leaf 141 [⟨1,[(3,1),(4,18)]⟩,⟨1,[(7,1)]⟩,⟨1,[(2,8),(3,1),(4,18)]⟩])) (.leaf 145 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1)]⟩]))
theorem target0ForwardRoot56_checked : checkTree [(-2,-1,0),(0,-1,-36),(1,0,-12),(1,2,72),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot56 = true := by decide

def target0ForwardRoot57 : CoverTree := .split (-5,-1,36) (.split (-5,-2,-18) (.leaf 141 [⟨2,[(2,3),(3,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(1,7),(2,2),(4,6)]⟩]) (.split (-7,-2,18) (.leaf 142 [⟨1,[(7,1)]⟩,⟨1,[(1,1),(4,6)]⟩,⟨1,[(6,1)]⟩]) (.leaf 145 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(0,1),(3,1)]⟩]))) (.leaf 146 [⟨1,[(3,1)]⟩,⟨1,[(0,1),(3,1)]⟩,⟨1,[(5,1)]⟩])
theorem target0ForwardRoot57_checked : checkTree [(-1,-2,-72),(1,0,-12),(1,1,36),(-1,1,72),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot57 = true := by decide

def target0ForwardRoot58 : CoverTree := .split (14,9,-240) (.split (-4,-3,66) (.split (-11,-9,150) (.leaf 167 [⟨1,[(0,1),(2,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 168 [⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩])) (.split (16,11,-306) (.leaf 183 [⟨2,[(0,1),(1,3)]⟩,⟨2,[(0,1),(1,9)]⟩,⟨1,[(7,1)]⟩]) (.leaf 182 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,4),(2,1),(4,30)]⟩]))) (.split (13,10,-144) (.split (-13,-9,192) (.leaf 163 [⟨1,[(7,1)]⟩,⟨1,[(2,3),(6,1),(4,6)]⟩,⟨1,[(6,1)]⟩]) (.leaf 166 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨14,[(2,27),(5,11),(4,108)]⟩])) (.leaf 162 [⟨3,[(0,2),(3,1),(4,36)]⟩,⟨1,[(6,1)]⟩,⟨3,[(0,1),(3,20),(4,18)]⟩]))
theorem target0ForwardRoot58_checked : checkTree [(-1,1,72),(-1,-1,12),(0,-1,-24),(2,1,-36),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot58 = true := by decide

def target0ForwardRoot59 : CoverTree := .split (13,6,-180) (.split (-13,-9,114) (.leaf 157 [⟨1,[(2,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.split (13,8,-162) (.split (-13,-7,210) (.leaf 161 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨3,[(0,7),(3,23),(4,108)]⟩]) (.leaf 162 [⟨1,[(2,1)]⟩,⟨3,[(0,7),(3,23),(4,108)]⟩,⟨1,[(8,1)]⟩])) (.leaf 158 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]))) (.split (13,9,-36) (.split (-13,-7,132) (.leaf 153 [⟨1,[(7,1)]⟩,⟨1,[(0,5),(1,8),(4,96)]⟩,⟨1,[(6,1)]⟩]) (.leaf 156 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨19,[(0,39),(5,22),(4,1014)]⟩])) (.leaf 152 [⟨1,[(2,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(0,7),(1,19),(4,72)]⟩]))
theorem target0ForwardRoot59_checked : checkTree [(1,-1,-72),(1,1,12),(0,1,48),(-2,-1,36),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot59 = true := by decide

def target0ForwardRoot60 : CoverTree := .split (-13,-10,144) (.leaf 162 [⟨1,[(1,1)]⟩,⟨1,[(5,1)]⟩,⟨2,[(0,13),(1,1)]⟩]) (.split (14,9,-240) (.leaf 167 [⟨1,[(2,1)]⟩,⟨2,[(2,13),(3,9)]⟩,⟨1,[(6,1)]⟩]) (.split (-13,-9,192) (.leaf 163 [⟨1,[(7,1)]⟩,⟨2,[(0,13),(1,1)]⟩,⟨1,[(5,1)]⟩]) (.leaf 166 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨2,[(2,13),(3,9)]⟩])))
theorem target0ForwardRoot60_checked : checkTree [(2,1,-36),(0,1,48),(-1,0,48),(-1,-2,-36),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot60 = true := by decide

def target0ForwardRoot61 : CoverTree := .split (11,9,-150) (.split (-2,-1,54) (.split (16,11,-306) (.leaf 183 [⟨1,[(6,1)]⟩,⟨1,[(2,3),(6,1)]⟩,⟨1,[(7,1)]⟩]) (.split (-4,-3,66) (.leaf 168 [⟨1,[(8,1)]⟩,⟨20,[(3,27),(5,23),(4,594)]⟩,⟨1,[(5,1)]⟩]) (.leaf 182 [⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(2,8),(8,1),(4,24)]⟩]))) (.split (-5,-1,198) (.leaf 180 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(2,3),(6,1)]⟩]) (.leaf 175 [⟨1,[(1,3),(6,1)]⟩,⟨1,[(1,2),(2,5),(4,6)]⟩,⟨1,[(7,1)]⟩]))) (.split (14,9,-240) (.leaf 167 [⟨1,[(1,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (13,10,-144) (.split (-13,-9,192) (.leaf 163 [⟨1,[(8,1)]⟩,⟨3,[(0,20),(3,19),(4,18)]⟩,⟨1,[(7,1)]⟩]) (.leaf 166 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩])) (.leaf 162 [⟨1,[(0,1),(2,1)]⟩,⟨1,[(7,1)]⟩,⟨3,[(0,20),(3,19),(4,18)]⟩])))
theorem target0ForwardRoot61_checked : checkTree [(1,2,36),(-1,0,48),(-1,-1,12),(1,-1,-72),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot61 = true := by decide

def target0ForwardRoot62 : CoverTree := .split (1,4,102) (.split (2,-1,-156) (.leaf 24 [⟨1,[(1,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(5,1)]⟩]) (.split (1,-2,-132) (.leaf 25 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩]) (.split (-1,3,168) (.leaf 172 [⟨1,[(2,1)]⟩,⟨2,[(2,1),(3,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 171 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨2,[(2,1),(3,1)]⟩])))) (.split (-1,4,234) (.split (0,1,42) (.split (2,-1,-156) (.leaf 23 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩]) (.split (1,-5,-258) (.leaf 22 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(9,1)]⟩]) (.leaf 26 [⟨7,[(3,6),(5,5),(4,18)]⟩,⟨1,[(9,1)]⟩,⟨1,[(5,1)]⟩]))) (.leaf 20 [⟨1,[(7,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 19 [⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(3,1)]⟩]))
theorem target0ForwardRoot62_checked : checkTree [(-1,1,108),(-1,-1,24),(0,-1,-36),(2,1,-72),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot62 = true := by decide

def target0ForwardRoot63 : CoverTree := .split (-1,5,258) (.split (-1,3,168) (.split (7,5,-162) (.split (-1,1,90) (.leaf 176 [⟨1,[(8,1)]⟩,⟨1,[(1,3),(8,1)]⟩,⟨1,[(7,1)]⟩]) (.split (-1,0,54) (.leaf 173 [⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(9,1)]⟩]) (.leaf 172 [⟨1,[(1,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(6,1)]⟩]))) (.leaf 175 [⟨13,[(6,6),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨2,[(2,9),(3,1)]⟩])) (.split (-1,2,132) (.split (-2,3,222) (.split (1,-1,-90) (.leaf 174 [⟨1,[(9,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 175 [⟨1,[(9,1)]⟩,⟨1,[(6,6),(9,13)]⟩,⟨1,[(2,6),(9,1)]⟩])) (.split (-1,0,54) (.leaf 170 [⟨1,[(7,1)]⟩,⟨1,[(9,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 171 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(9,1)]⟩]))) (.split (-1,-4,-102) (.leaf 26 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩]) (.leaf 25 [⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩,⟨7,[(0,9),(8,4),(4,36)]⟩])))) (.split (-1,-5,-162) (.leaf 18 [⟨1,[(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩]) (.split (0,-1,-42) (.leaf 21 [⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,1)]⟩]) (.leaf 22 [⟨1,[(7,1)]⟩,⟨1,[(0,1),(7,2)]⟩,⟨1,[(5,1)]⟩])))
theorem target0ForwardRoot63_checked : checkTree [(-2,-1,72),(0,-1,-36),(1,0,-48),(1,2,36),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot63 = true := by decide

theorem targetKiteFamily0Chunk7_covered : FamilyCover targetKiteFamily0Chunk7 targetMeshFamily0 := by
  intro p hp
  simp only [targetKiteFamily0Chunk7,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨target0ForwardRoot56,target0ForwardRoot56_checked⟩
  · exact ⟨target0ForwardRoot57,target0ForwardRoot57_checked⟩
  · exact ⟨target0ForwardRoot58,target0ForwardRoot58_checked⟩
  · exact ⟨target0ForwardRoot59,target0ForwardRoot59_checked⟩
  · exact ⟨target0ForwardRoot60,target0ForwardRoot60_checked⟩
  · exact ⟨target0ForwardRoot61,target0ForwardRoot61_checked⟩
  · exact ⟨target0ForwardRoot62,target0ForwardRoot62_checked⟩
  · exact ⟨target0ForwardRoot63,target0ForwardRoot63_checked⟩

def target0ForwardRoot64 : CoverTree := .split (7,5,-162) (.split (-4,-5,54) (.split (-1,-1,18) (.leaf 178 [⟨1,[(7,1)]⟩,⟨1,[(5,1)]⟩,⟨1,[(3,2),(7,3)]⟩]) (.leaf 29 [⟨1,[(7,1)]⟩,⟨1,[(3,1)]⟩,⟨1,[(6,1)]⟩])) (.leaf 28 [⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(3,1)]⟩])) (.split (-2,-1,54) (.split (5,4,-90) (.leaf 184 [⟨1,[(6,1)]⟩,⟨1,[(0,2),(6,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 183 [⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(1,5),(2,11),(4,6)]⟩])) (.leaf 179 [⟨1,[(6,1)]⟩,⟨1,[(3,1),(6,1)]⟩,⟨1,[(5,1)]⟩]))
theorem target0ForwardRoot64_checked : checkTree [(-1,-2,0),(1,0,-36),(1,1,-12),(-1,1,72),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot64 = true := by decide

def target0ForwardRoot65 : CoverTree := .split (-1,-1,18) (.split (1,2,18) (.split (5,1,-198) (.leaf 177 [⟨1,[(5,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(6,1)]⟩]) (.split (7,5,-162) (.leaf 178 [⟨1,[(5,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(7,1)]⟩]) (.leaf 179 [⟨1,[(0,1),(6,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(8,1)]⟩]))) (.split (7,5,-162) (.leaf 176 [⟨1,[(2,2),(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(7,1)]⟩]) (.split (-5,-1,198) (.leaf 180 [⟨1,[(1,3),(6,1)]⟩,⟨1,[(8,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 175 [⟨1,[(1,6),(7,1)]⟩,⟨1,[(7,1)]⟩,⟨1,[(8,1)]⟩])))) (.split (5,4,-126) (.leaf 27 [⟨1,[(3,1)]⟩,⟨1,[(0,1)]⟩,⟨1,[(6,1)]⟩]) (.leaf 30 [⟨1,[(5,1)]⟩,⟨1,[(6,1)]⟩,⟨1,[(0,1)]⟩]))
theorem target0ForwardRoot65_checked : checkTree [(1,-1,-72),(1,1,-12),(0,1,36),(-2,-1,72),(0,0,1)] (familyFacets targetMeshFamily0) target0ForwardRoot65 = true := by decide

theorem targetKiteFamily0Chunk8_covered : FamilyCover targetKiteFamily0Chunk8 targetMeshFamily0 := by
  intro p hp
  simp only [targetKiteFamily0Chunk8,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨target0ForwardRoot64,target0ForwardRoot64_checked⟩
  · exact ⟨target0ForwardRoot65,target0ForwardRoot65_checked⟩


end SpectreGeometry.ReverseClusterTriangulation
