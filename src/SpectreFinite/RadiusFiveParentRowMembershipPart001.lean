module

public import SpectreFinite.ParentOwnershipFinite

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem parentChunk_mem008 : ParentOwnership.parentRows008 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 8) (by decide)
theorem parentRow_mem0128 : ParentOwnership.parentRow0128 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 0) (by decide)
theorem parentRow_mem0129 : ParentOwnership.parentRow0129 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 1) (by decide)
theorem parentRow_mem0130 : ParentOwnership.parentRow0130 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 2) (by decide)
theorem parentRow_mem0131 : ParentOwnership.parentRow0131 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 3) (by decide)
theorem parentRow_mem0132 : ParentOwnership.parentRow0132 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 4) (by decide)
theorem parentRow_mem0133 : ParentOwnership.parentRow0133 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 5) (by decide)
theorem parentRow_mem0134 : ParentOwnership.parentRow0134 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 6) (by decide)
theorem parentRow_mem0135 : ParentOwnership.parentRow0135 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 7) (by decide)
theorem parentRow_mem0136 : ParentOwnership.parentRow0136 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 8) (by decide)
theorem parentRow_mem0137 : ParentOwnership.parentRow0137 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 9) (by decide)
theorem parentRow_mem0138 : ParentOwnership.parentRow0138 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 10) (by decide)
theorem parentRow_mem0139 : ParentOwnership.parentRow0139 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 11) (by decide)
theorem parentRow_mem0140 : ParentOwnership.parentRow0140 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 12) (by decide)
theorem parentRow_mem0141 : ParentOwnership.parentRow0141 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 13) (by decide)
theorem parentRow_mem0142 : ParentOwnership.parentRow0142 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 14) (by decide)
theorem parentRow_mem0143 : ParentOwnership.parentRow0143 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows008, parentChunk_mem008, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows008) (n := 15) (by decide)
theorem parentChunk_mem009 : ParentOwnership.parentRows009 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 9) (by decide)
theorem parentRow_mem0144 : ParentOwnership.parentRow0144 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 0) (by decide)
theorem parentRow_mem0145 : ParentOwnership.parentRow0145 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 1) (by decide)
theorem parentRow_mem0146 : ParentOwnership.parentRow0146 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 2) (by decide)
theorem parentRow_mem0147 : ParentOwnership.parentRow0147 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 3) (by decide)
theorem parentRow_mem0148 : ParentOwnership.parentRow0148 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 4) (by decide)
theorem parentRow_mem0149 : ParentOwnership.parentRow0149 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 5) (by decide)
theorem parentRow_mem0150 : ParentOwnership.parentRow0150 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 6) (by decide)
theorem parentRow_mem0151 : ParentOwnership.parentRow0151 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 7) (by decide)
theorem parentRow_mem0152 : ParentOwnership.parentRow0152 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 8) (by decide)
theorem parentRow_mem0153 : ParentOwnership.parentRow0153 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 9) (by decide)
theorem parentRow_mem0154 : ParentOwnership.parentRow0154 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 10) (by decide)
theorem parentRow_mem0155 : ParentOwnership.parentRow0155 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 11) (by decide)
theorem parentRow_mem0156 : ParentOwnership.parentRow0156 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 12) (by decide)
theorem parentRow_mem0157 : ParentOwnership.parentRow0157 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 13) (by decide)
theorem parentRow_mem0158 : ParentOwnership.parentRow0158 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 14) (by decide)
theorem parentRow_mem0159 : ParentOwnership.parentRow0159 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows009, parentChunk_mem009, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows009) (n := 15) (by decide)
theorem parentChunk_mem010 : ParentOwnership.parentRows010 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 10) (by decide)
theorem parentRow_mem0160 : ParentOwnership.parentRow0160 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 0) (by decide)
theorem parentRow_mem0161 : ParentOwnership.parentRow0161 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 1) (by decide)
theorem parentRow_mem0162 : ParentOwnership.parentRow0162 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 2) (by decide)
theorem parentRow_mem0163 : ParentOwnership.parentRow0163 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 3) (by decide)
theorem parentRow_mem0164 : ParentOwnership.parentRow0164 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 4) (by decide)
theorem parentRow_mem0165 : ParentOwnership.parentRow0165 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 5) (by decide)
theorem parentRow_mem0166 : ParentOwnership.parentRow0166 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 6) (by decide)
theorem parentRow_mem0167 : ParentOwnership.parentRow0167 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 7) (by decide)
theorem parentRow_mem0168 : ParentOwnership.parentRow0168 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 8) (by decide)
theorem parentRow_mem0169 : ParentOwnership.parentRow0169 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 9) (by decide)
theorem parentRow_mem0170 : ParentOwnership.parentRow0170 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 10) (by decide)
theorem parentRow_mem0171 : ParentOwnership.parentRow0171 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 11) (by decide)
theorem parentRow_mem0172 : ParentOwnership.parentRow0172 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 12) (by decide)
theorem parentRow_mem0173 : ParentOwnership.parentRow0173 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 13) (by decide)
theorem parentRow_mem0174 : ParentOwnership.parentRow0174 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 14) (by decide)
theorem parentRow_mem0175 : ParentOwnership.parentRow0175 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows010, parentChunk_mem010, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows010) (n := 15) (by decide)
theorem parentChunk_mem011 : ParentOwnership.parentRows011 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 11) (by decide)
theorem parentRow_mem0176 : ParentOwnership.parentRow0176 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 0) (by decide)
theorem parentRow_mem0177 : ParentOwnership.parentRow0177 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 1) (by decide)
theorem parentRow_mem0178 : ParentOwnership.parentRow0178 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 2) (by decide)
theorem parentRow_mem0179 : ParentOwnership.parentRow0179 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 3) (by decide)
theorem parentRow_mem0180 : ParentOwnership.parentRow0180 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 4) (by decide)
theorem parentRow_mem0181 : ParentOwnership.parentRow0181 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 5) (by decide)
theorem parentRow_mem0182 : ParentOwnership.parentRow0182 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 6) (by decide)
theorem parentRow_mem0183 : ParentOwnership.parentRow0183 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 7) (by decide)
theorem parentRow_mem0184 : ParentOwnership.parentRow0184 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 8) (by decide)
theorem parentRow_mem0185 : ParentOwnership.parentRow0185 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 9) (by decide)
theorem parentRow_mem0186 : ParentOwnership.parentRow0186 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 10) (by decide)
theorem parentRow_mem0187 : ParentOwnership.parentRow0187 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 11) (by decide)
theorem parentRow_mem0188 : ParentOwnership.parentRow0188 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 12) (by decide)
theorem parentRow_mem0189 : ParentOwnership.parentRow0189 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 13) (by decide)
theorem parentRow_mem0190 : ParentOwnership.parentRow0190 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 14) (by decide)
theorem parentRow_mem0191 : ParentOwnership.parentRow0191 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows011, parentChunk_mem011, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows011) (n := 15) (by decide)
theorem parentChunk_mem012 : ParentOwnership.parentRows012 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 12) (by decide)
theorem parentRow_mem0192 : ParentOwnership.parentRow0192 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 0) (by decide)
theorem parentRow_mem0193 : ParentOwnership.parentRow0193 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 1) (by decide)
theorem parentRow_mem0194 : ParentOwnership.parentRow0194 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 2) (by decide)
theorem parentRow_mem0195 : ParentOwnership.parentRow0195 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 3) (by decide)
theorem parentRow_mem0196 : ParentOwnership.parentRow0196 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 4) (by decide)
theorem parentRow_mem0197 : ParentOwnership.parentRow0197 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 5) (by decide)
theorem parentRow_mem0198 : ParentOwnership.parentRow0198 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 6) (by decide)
theorem parentRow_mem0199 : ParentOwnership.parentRow0199 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 7) (by decide)
theorem parentRow_mem0200 : ParentOwnership.parentRow0200 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 8) (by decide)
theorem parentRow_mem0201 : ParentOwnership.parentRow0201 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 9) (by decide)
theorem parentRow_mem0202 : ParentOwnership.parentRow0202 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 10) (by decide)
theorem parentRow_mem0203 : ParentOwnership.parentRow0203 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 11) (by decide)
theorem parentRow_mem0204 : ParentOwnership.parentRow0204 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 12) (by decide)
theorem parentRow_mem0205 : ParentOwnership.parentRow0205 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 13) (by decide)
theorem parentRow_mem0206 : ParentOwnership.parentRow0206 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 14) (by decide)
theorem parentRow_mem0207 : ParentOwnership.parentRow0207 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows012, parentChunk_mem012, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows012) (n := 15) (by decide)
theorem parentChunk_mem013 : ParentOwnership.parentRows013 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 13) (by decide)
theorem parentRow_mem0208 : ParentOwnership.parentRow0208 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 0) (by decide)
theorem parentRow_mem0209 : ParentOwnership.parentRow0209 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 1) (by decide)
theorem parentRow_mem0210 : ParentOwnership.parentRow0210 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 2) (by decide)
theorem parentRow_mem0211 : ParentOwnership.parentRow0211 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 3) (by decide)
theorem parentRow_mem0212 : ParentOwnership.parentRow0212 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 4) (by decide)
theorem parentRow_mem0213 : ParentOwnership.parentRow0213 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 5) (by decide)
theorem parentRow_mem0214 : ParentOwnership.parentRow0214 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 6) (by decide)
theorem parentRow_mem0215 : ParentOwnership.parentRow0215 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 7) (by decide)
theorem parentRow_mem0216 : ParentOwnership.parentRow0216 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 8) (by decide)
theorem parentRow_mem0217 : ParentOwnership.parentRow0217 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 9) (by decide)
theorem parentRow_mem0218 : ParentOwnership.parentRow0218 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 10) (by decide)
theorem parentRow_mem0219 : ParentOwnership.parentRow0219 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 11) (by decide)
theorem parentRow_mem0220 : ParentOwnership.parentRow0220 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 12) (by decide)
theorem parentRow_mem0221 : ParentOwnership.parentRow0221 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 13) (by decide)
theorem parentRow_mem0222 : ParentOwnership.parentRow0222 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 14) (by decide)
theorem parentRow_mem0223 : ParentOwnership.parentRow0223 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows013, parentChunk_mem013, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows013) (n := 15) (by decide)
theorem parentChunk_mem014 : ParentOwnership.parentRows014 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 14) (by decide)
theorem parentRow_mem0224 : ParentOwnership.parentRow0224 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 0) (by decide)
theorem parentRow_mem0225 : ParentOwnership.parentRow0225 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 1) (by decide)
theorem parentRow_mem0226 : ParentOwnership.parentRow0226 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 2) (by decide)
theorem parentRow_mem0227 : ParentOwnership.parentRow0227 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 3) (by decide)
theorem parentRow_mem0228 : ParentOwnership.parentRow0228 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 4) (by decide)
theorem parentRow_mem0229 : ParentOwnership.parentRow0229 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 5) (by decide)
theorem parentRow_mem0230 : ParentOwnership.parentRow0230 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 6) (by decide)
theorem parentRow_mem0231 : ParentOwnership.parentRow0231 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 7) (by decide)
theorem parentRow_mem0232 : ParentOwnership.parentRow0232 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 8) (by decide)
theorem parentRow_mem0233 : ParentOwnership.parentRow0233 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 9) (by decide)
theorem parentRow_mem0234 : ParentOwnership.parentRow0234 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 10) (by decide)
theorem parentRow_mem0235 : ParentOwnership.parentRow0235 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 11) (by decide)
theorem parentRow_mem0236 : ParentOwnership.parentRow0236 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 12) (by decide)
theorem parentRow_mem0237 : ParentOwnership.parentRow0237 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 13) (by decide)
theorem parentRow_mem0238 : ParentOwnership.parentRow0238 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 14) (by decide)
theorem parentRow_mem0239 : ParentOwnership.parentRow0239 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows014, parentChunk_mem014, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows014) (n := 15) (by decide)
theorem parentChunk_mem015 : ParentOwnership.parentRows015 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 15) (by decide)
theorem parentRow_mem0240 : ParentOwnership.parentRow0240 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 0) (by decide)
theorem parentRow_mem0241 : ParentOwnership.parentRow0241 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 1) (by decide)
theorem parentRow_mem0242 : ParentOwnership.parentRow0242 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 2) (by decide)
theorem parentRow_mem0243 : ParentOwnership.parentRow0243 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 3) (by decide)
theorem parentRow_mem0244 : ParentOwnership.parentRow0244 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 4) (by decide)
theorem parentRow_mem0245 : ParentOwnership.parentRow0245 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 5) (by decide)
theorem parentRow_mem0246 : ParentOwnership.parentRow0246 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 6) (by decide)
theorem parentRow_mem0247 : ParentOwnership.parentRow0247 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 7) (by decide)
theorem parentRow_mem0248 : ParentOwnership.parentRow0248 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 8) (by decide)
theorem parentRow_mem0249 : ParentOwnership.parentRow0249 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 9) (by decide)
theorem parentRow_mem0250 : ParentOwnership.parentRow0250 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 10) (by decide)
theorem parentRow_mem0251 : ParentOwnership.parentRow0251 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 11) (by decide)
theorem parentRow_mem0252 : ParentOwnership.parentRow0252 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 12) (by decide)
theorem parentRow_mem0253 : ParentOwnership.parentRow0253 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 13) (by decide)
theorem parentRow_mem0254 : ParentOwnership.parentRow0254 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 14) (by decide)
theorem parentRow_mem0255 : ParentOwnership.parentRow0255 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows015, parentChunk_mem015, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows015) (n := 15) (by decide)

end SpectreFinite.HexSearch.RadiusFiveParentBinding
