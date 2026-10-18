module

public import SpectreFinite.ParentOwnershipFinite

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem parentChunk_mem000 : ParentOwnership.parentRows000 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 0) (by decide)
theorem parentRow_mem0000 : ParentOwnership.parentRow0000 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 0) (by decide)
theorem parentRow_mem0001 : ParentOwnership.parentRow0001 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 1) (by decide)
theorem parentRow_mem0002 : ParentOwnership.parentRow0002 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 2) (by decide)
theorem parentRow_mem0003 : ParentOwnership.parentRow0003 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 3) (by decide)
theorem parentRow_mem0004 : ParentOwnership.parentRow0004 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 4) (by decide)
theorem parentRow_mem0005 : ParentOwnership.parentRow0005 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 5) (by decide)
theorem parentRow_mem0006 : ParentOwnership.parentRow0006 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 6) (by decide)
theorem parentRow_mem0007 : ParentOwnership.parentRow0007 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 7) (by decide)
theorem parentRow_mem0008 : ParentOwnership.parentRow0008 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 8) (by decide)
theorem parentRow_mem0009 : ParentOwnership.parentRow0009 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 9) (by decide)
theorem parentRow_mem0010 : ParentOwnership.parentRow0010 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 10) (by decide)
theorem parentRow_mem0011 : ParentOwnership.parentRow0011 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 11) (by decide)
theorem parentRow_mem0012 : ParentOwnership.parentRow0012 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 12) (by decide)
theorem parentRow_mem0013 : ParentOwnership.parentRow0013 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 13) (by decide)
theorem parentRow_mem0014 : ParentOwnership.parentRow0014 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 14) (by decide)
theorem parentRow_mem0015 : ParentOwnership.parentRow0015 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows000, parentChunk_mem000, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows000) (n := 15) (by decide)
theorem parentChunk_mem001 : ParentOwnership.parentRows001 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 1) (by decide)
theorem parentRow_mem0016 : ParentOwnership.parentRow0016 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 0) (by decide)
theorem parentRow_mem0017 : ParentOwnership.parentRow0017 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 1) (by decide)
theorem parentRow_mem0018 : ParentOwnership.parentRow0018 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 2) (by decide)
theorem parentRow_mem0019 : ParentOwnership.parentRow0019 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 3) (by decide)
theorem parentRow_mem0020 : ParentOwnership.parentRow0020 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 4) (by decide)
theorem parentRow_mem0021 : ParentOwnership.parentRow0021 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 5) (by decide)
theorem parentRow_mem0022 : ParentOwnership.parentRow0022 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 6) (by decide)
theorem parentRow_mem0023 : ParentOwnership.parentRow0023 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 7) (by decide)
theorem parentRow_mem0024 : ParentOwnership.parentRow0024 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 8) (by decide)
theorem parentRow_mem0025 : ParentOwnership.parentRow0025 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 9) (by decide)
theorem parentRow_mem0026 : ParentOwnership.parentRow0026 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 10) (by decide)
theorem parentRow_mem0027 : ParentOwnership.parentRow0027 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 11) (by decide)
theorem parentRow_mem0028 : ParentOwnership.parentRow0028 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 12) (by decide)
theorem parentRow_mem0029 : ParentOwnership.parentRow0029 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 13) (by decide)
theorem parentRow_mem0030 : ParentOwnership.parentRow0030 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 14) (by decide)
theorem parentRow_mem0031 : ParentOwnership.parentRow0031 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows001, parentChunk_mem001, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows001) (n := 15) (by decide)
theorem parentChunk_mem002 : ParentOwnership.parentRows002 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 2) (by decide)
theorem parentRow_mem0032 : ParentOwnership.parentRow0032 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 0) (by decide)
theorem parentRow_mem0033 : ParentOwnership.parentRow0033 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 1) (by decide)
theorem parentRow_mem0034 : ParentOwnership.parentRow0034 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 2) (by decide)
theorem parentRow_mem0035 : ParentOwnership.parentRow0035 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 3) (by decide)
theorem parentRow_mem0036 : ParentOwnership.parentRow0036 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 4) (by decide)
theorem parentRow_mem0037 : ParentOwnership.parentRow0037 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 5) (by decide)
theorem parentRow_mem0038 : ParentOwnership.parentRow0038 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 6) (by decide)
theorem parentRow_mem0039 : ParentOwnership.parentRow0039 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 7) (by decide)
theorem parentRow_mem0040 : ParentOwnership.parentRow0040 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 8) (by decide)
theorem parentRow_mem0041 : ParentOwnership.parentRow0041 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 9) (by decide)
theorem parentRow_mem0042 : ParentOwnership.parentRow0042 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 10) (by decide)
theorem parentRow_mem0043 : ParentOwnership.parentRow0043 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 11) (by decide)
theorem parentRow_mem0044 : ParentOwnership.parentRow0044 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 12) (by decide)
theorem parentRow_mem0045 : ParentOwnership.parentRow0045 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 13) (by decide)
theorem parentRow_mem0046 : ParentOwnership.parentRow0046 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 14) (by decide)
theorem parentRow_mem0047 : ParentOwnership.parentRow0047 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows002, parentChunk_mem002, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows002) (n := 15) (by decide)
theorem parentChunk_mem003 : ParentOwnership.parentRows003 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 3) (by decide)
theorem parentRow_mem0048 : ParentOwnership.parentRow0048 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 0) (by decide)
theorem parentRow_mem0049 : ParentOwnership.parentRow0049 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 1) (by decide)
theorem parentRow_mem0050 : ParentOwnership.parentRow0050 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 2) (by decide)
theorem parentRow_mem0051 : ParentOwnership.parentRow0051 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 3) (by decide)
theorem parentRow_mem0052 : ParentOwnership.parentRow0052 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 4) (by decide)
theorem parentRow_mem0053 : ParentOwnership.parentRow0053 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 5) (by decide)
theorem parentRow_mem0054 : ParentOwnership.parentRow0054 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 6) (by decide)
theorem parentRow_mem0055 : ParentOwnership.parentRow0055 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 7) (by decide)
theorem parentRow_mem0056 : ParentOwnership.parentRow0056 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 8) (by decide)
theorem parentRow_mem0057 : ParentOwnership.parentRow0057 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 9) (by decide)
theorem parentRow_mem0058 : ParentOwnership.parentRow0058 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 10) (by decide)
theorem parentRow_mem0059 : ParentOwnership.parentRow0059 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 11) (by decide)
theorem parentRow_mem0060 : ParentOwnership.parentRow0060 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 12) (by decide)
theorem parentRow_mem0061 : ParentOwnership.parentRow0061 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 13) (by decide)
theorem parentRow_mem0062 : ParentOwnership.parentRow0062 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 14) (by decide)
theorem parentRow_mem0063 : ParentOwnership.parentRow0063 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows003, parentChunk_mem003, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows003) (n := 15) (by decide)
theorem parentChunk_mem004 : ParentOwnership.parentRows004 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 4) (by decide)
theorem parentRow_mem0064 : ParentOwnership.parentRow0064 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 0) (by decide)
theorem parentRow_mem0065 : ParentOwnership.parentRow0065 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 1) (by decide)
theorem parentRow_mem0066 : ParentOwnership.parentRow0066 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 2) (by decide)
theorem parentRow_mem0067 : ParentOwnership.parentRow0067 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 3) (by decide)
theorem parentRow_mem0068 : ParentOwnership.parentRow0068 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 4) (by decide)
theorem parentRow_mem0069 : ParentOwnership.parentRow0069 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 5) (by decide)
theorem parentRow_mem0070 : ParentOwnership.parentRow0070 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 6) (by decide)
theorem parentRow_mem0071 : ParentOwnership.parentRow0071 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 7) (by decide)
theorem parentRow_mem0072 : ParentOwnership.parentRow0072 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 8) (by decide)
theorem parentRow_mem0073 : ParentOwnership.parentRow0073 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 9) (by decide)
theorem parentRow_mem0074 : ParentOwnership.parentRow0074 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 10) (by decide)
theorem parentRow_mem0075 : ParentOwnership.parentRow0075 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 11) (by decide)
theorem parentRow_mem0076 : ParentOwnership.parentRow0076 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 12) (by decide)
theorem parentRow_mem0077 : ParentOwnership.parentRow0077 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 13) (by decide)
theorem parentRow_mem0078 : ParentOwnership.parentRow0078 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 14) (by decide)
theorem parentRow_mem0079 : ParentOwnership.parentRow0079 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows004, parentChunk_mem004, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows004) (n := 15) (by decide)
theorem parentChunk_mem005 : ParentOwnership.parentRows005 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 5) (by decide)
theorem parentRow_mem0080 : ParentOwnership.parentRow0080 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 0) (by decide)
theorem parentRow_mem0081 : ParentOwnership.parentRow0081 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 1) (by decide)
theorem parentRow_mem0082 : ParentOwnership.parentRow0082 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 2) (by decide)
theorem parentRow_mem0083 : ParentOwnership.parentRow0083 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 3) (by decide)
theorem parentRow_mem0084 : ParentOwnership.parentRow0084 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 4) (by decide)
theorem parentRow_mem0085 : ParentOwnership.parentRow0085 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 5) (by decide)
theorem parentRow_mem0086 : ParentOwnership.parentRow0086 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 6) (by decide)
theorem parentRow_mem0087 : ParentOwnership.parentRow0087 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 7) (by decide)
theorem parentRow_mem0088 : ParentOwnership.parentRow0088 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 8) (by decide)
theorem parentRow_mem0089 : ParentOwnership.parentRow0089 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 9) (by decide)
theorem parentRow_mem0090 : ParentOwnership.parentRow0090 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 10) (by decide)
theorem parentRow_mem0091 : ParentOwnership.parentRow0091 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 11) (by decide)
theorem parentRow_mem0092 : ParentOwnership.parentRow0092 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 12) (by decide)
theorem parentRow_mem0093 : ParentOwnership.parentRow0093 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 13) (by decide)
theorem parentRow_mem0094 : ParentOwnership.parentRow0094 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 14) (by decide)
theorem parentRow_mem0095 : ParentOwnership.parentRow0095 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows005, parentChunk_mem005, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows005) (n := 15) (by decide)
theorem parentChunk_mem006 : ParentOwnership.parentRows006 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 6) (by decide)
theorem parentRow_mem0096 : ParentOwnership.parentRow0096 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 0) (by decide)
theorem parentRow_mem0097 : ParentOwnership.parentRow0097 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 1) (by decide)
theorem parentRow_mem0098 : ParentOwnership.parentRow0098 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 2) (by decide)
theorem parentRow_mem0099 : ParentOwnership.parentRow0099 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 3) (by decide)
theorem parentRow_mem0100 : ParentOwnership.parentRow0100 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 4) (by decide)
theorem parentRow_mem0101 : ParentOwnership.parentRow0101 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 5) (by decide)
theorem parentRow_mem0102 : ParentOwnership.parentRow0102 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 6) (by decide)
theorem parentRow_mem0103 : ParentOwnership.parentRow0103 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 7) (by decide)
theorem parentRow_mem0104 : ParentOwnership.parentRow0104 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 8) (by decide)
theorem parentRow_mem0105 : ParentOwnership.parentRow0105 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 9) (by decide)
theorem parentRow_mem0106 : ParentOwnership.parentRow0106 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 10) (by decide)
theorem parentRow_mem0107 : ParentOwnership.parentRow0107 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 11) (by decide)
theorem parentRow_mem0108 : ParentOwnership.parentRow0108 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 12) (by decide)
theorem parentRow_mem0109 : ParentOwnership.parentRow0109 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 13) (by decide)
theorem parentRow_mem0110 : ParentOwnership.parentRow0110 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 14) (by decide)
theorem parentRow_mem0111 : ParentOwnership.parentRow0111 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows006, parentChunk_mem006, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows006) (n := 15) (by decide)
theorem parentChunk_mem007 : ParentOwnership.parentRows007 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 7) (by decide)
theorem parentRow_mem0112 : ParentOwnership.parentRow0112 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 0) (by decide)
theorem parentRow_mem0113 : ParentOwnership.parentRow0113 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 1) (by decide)
theorem parentRow_mem0114 : ParentOwnership.parentRow0114 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 2) (by decide)
theorem parentRow_mem0115 : ParentOwnership.parentRow0115 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 3) (by decide)
theorem parentRow_mem0116 : ParentOwnership.parentRow0116 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 4) (by decide)
theorem parentRow_mem0117 : ParentOwnership.parentRow0117 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 5) (by decide)
theorem parentRow_mem0118 : ParentOwnership.parentRow0118 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 6) (by decide)
theorem parentRow_mem0119 : ParentOwnership.parentRow0119 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 7) (by decide)
theorem parentRow_mem0120 : ParentOwnership.parentRow0120 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 8) (by decide)
theorem parentRow_mem0121 : ParentOwnership.parentRow0121 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 9) (by decide)
theorem parentRow_mem0122 : ParentOwnership.parentRow0122 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 10) (by decide)
theorem parentRow_mem0123 : ParentOwnership.parentRow0123 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 11) (by decide)
theorem parentRow_mem0124 : ParentOwnership.parentRow0124 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 12) (by decide)
theorem parentRow_mem0125 : ParentOwnership.parentRow0125 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 13) (by decide)
theorem parentRow_mem0126 : ParentOwnership.parentRow0126 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 14) (by decide)
theorem parentRow_mem0127 : ParentOwnership.parentRow0127 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows007, parentChunk_mem007, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows007) (n := 15) (by decide)

end SpectreFinite.HexSearch.RadiusFiveParentBinding
