module

public import SpectreFinite.ParentOwnershipFinite

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem parentChunk_mem128 : ParentOwnership.parentRows128 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 128) (by decide)
theorem parentRow_mem2048 : ParentOwnership.parentRow2048 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 0) (by decide)
theorem parentRow_mem2049 : ParentOwnership.parentRow2049 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 1) (by decide)
theorem parentRow_mem2050 : ParentOwnership.parentRow2050 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 2) (by decide)
theorem parentRow_mem2051 : ParentOwnership.parentRow2051 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 3) (by decide)
theorem parentRow_mem2052 : ParentOwnership.parentRow2052 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 4) (by decide)
theorem parentRow_mem2053 : ParentOwnership.parentRow2053 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 5) (by decide)
theorem parentRow_mem2054 : ParentOwnership.parentRow2054 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 6) (by decide)
theorem parentRow_mem2055 : ParentOwnership.parentRow2055 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 7) (by decide)
theorem parentRow_mem2056 : ParentOwnership.parentRow2056 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 8) (by decide)
theorem parentRow_mem2057 : ParentOwnership.parentRow2057 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 9) (by decide)
theorem parentRow_mem2058 : ParentOwnership.parentRow2058 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 10) (by decide)
theorem parentRow_mem2059 : ParentOwnership.parentRow2059 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 11) (by decide)
theorem parentRow_mem2060 : ParentOwnership.parentRow2060 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 12) (by decide)
theorem parentRow_mem2061 : ParentOwnership.parentRow2061 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 13) (by decide)
theorem parentRow_mem2062 : ParentOwnership.parentRow2062 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 14) (by decide)
theorem parentRow_mem2063 : ParentOwnership.parentRow2063 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows128, parentChunk_mem128, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows128) (n := 15) (by decide)
theorem parentChunk_mem129 : ParentOwnership.parentRows129 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 129) (by decide)
theorem parentRow_mem2064 : ParentOwnership.parentRow2064 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 0) (by decide)
theorem parentRow_mem2065 : ParentOwnership.parentRow2065 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 1) (by decide)
theorem parentRow_mem2066 : ParentOwnership.parentRow2066 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 2) (by decide)
theorem parentRow_mem2067 : ParentOwnership.parentRow2067 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 3) (by decide)
theorem parentRow_mem2068 : ParentOwnership.parentRow2068 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 4) (by decide)
theorem parentRow_mem2069 : ParentOwnership.parentRow2069 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 5) (by decide)
theorem parentRow_mem2070 : ParentOwnership.parentRow2070 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 6) (by decide)
theorem parentRow_mem2071 : ParentOwnership.parentRow2071 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 7) (by decide)
theorem parentRow_mem2072 : ParentOwnership.parentRow2072 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 8) (by decide)
theorem parentRow_mem2073 : ParentOwnership.parentRow2073 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 9) (by decide)
theorem parentRow_mem2074 : ParentOwnership.parentRow2074 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 10) (by decide)
theorem parentRow_mem2075 : ParentOwnership.parentRow2075 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 11) (by decide)
theorem parentRow_mem2076 : ParentOwnership.parentRow2076 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 12) (by decide)
theorem parentRow_mem2077 : ParentOwnership.parentRow2077 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 13) (by decide)
theorem parentRow_mem2078 : ParentOwnership.parentRow2078 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 14) (by decide)
theorem parentRow_mem2079 : ParentOwnership.parentRow2079 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows129, parentChunk_mem129, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows129) (n := 15) (by decide)
theorem parentChunk_mem130 : ParentOwnership.parentRows130 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 130) (by decide)
theorem parentRow_mem2080 : ParentOwnership.parentRow2080 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 0) (by decide)
theorem parentRow_mem2081 : ParentOwnership.parentRow2081 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 1) (by decide)
theorem parentRow_mem2082 : ParentOwnership.parentRow2082 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 2) (by decide)
theorem parentRow_mem2083 : ParentOwnership.parentRow2083 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 3) (by decide)
theorem parentRow_mem2084 : ParentOwnership.parentRow2084 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 4) (by decide)
theorem parentRow_mem2085 : ParentOwnership.parentRow2085 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 5) (by decide)
theorem parentRow_mem2086 : ParentOwnership.parentRow2086 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 6) (by decide)
theorem parentRow_mem2087 : ParentOwnership.parentRow2087 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 7) (by decide)
theorem parentRow_mem2088 : ParentOwnership.parentRow2088 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 8) (by decide)
theorem parentRow_mem2089 : ParentOwnership.parentRow2089 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 9) (by decide)
theorem parentRow_mem2090 : ParentOwnership.parentRow2090 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 10) (by decide)
theorem parentRow_mem2091 : ParentOwnership.parentRow2091 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 11) (by decide)
theorem parentRow_mem2092 : ParentOwnership.parentRow2092 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 12) (by decide)
theorem parentRow_mem2093 : ParentOwnership.parentRow2093 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 13) (by decide)
theorem parentRow_mem2094 : ParentOwnership.parentRow2094 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 14) (by decide)
theorem parentRow_mem2095 : ParentOwnership.parentRow2095 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows130, parentChunk_mem130, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows130) (n := 15) (by decide)
theorem parentChunk_mem131 : ParentOwnership.parentRows131 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 131) (by decide)
theorem parentRow_mem2096 : ParentOwnership.parentRow2096 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 0) (by decide)
theorem parentRow_mem2097 : ParentOwnership.parentRow2097 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 1) (by decide)
theorem parentRow_mem2098 : ParentOwnership.parentRow2098 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 2) (by decide)
theorem parentRow_mem2099 : ParentOwnership.parentRow2099 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 3) (by decide)
theorem parentRow_mem2100 : ParentOwnership.parentRow2100 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 4) (by decide)
theorem parentRow_mem2101 : ParentOwnership.parentRow2101 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 5) (by decide)
theorem parentRow_mem2102 : ParentOwnership.parentRow2102 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 6) (by decide)
theorem parentRow_mem2103 : ParentOwnership.parentRow2103 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 7) (by decide)
theorem parentRow_mem2104 : ParentOwnership.parentRow2104 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 8) (by decide)
theorem parentRow_mem2105 : ParentOwnership.parentRow2105 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 9) (by decide)
theorem parentRow_mem2106 : ParentOwnership.parentRow2106 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 10) (by decide)
theorem parentRow_mem2107 : ParentOwnership.parentRow2107 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 11) (by decide)
theorem parentRow_mem2108 : ParentOwnership.parentRow2108 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 12) (by decide)
theorem parentRow_mem2109 : ParentOwnership.parentRow2109 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 13) (by decide)
theorem parentRow_mem2110 : ParentOwnership.parentRow2110 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 14) (by decide)
theorem parentRow_mem2111 : ParentOwnership.parentRow2111 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows131, parentChunk_mem131, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows131) (n := 15) (by decide)

end SpectreFinite.HexSearch.RadiusFiveParentBinding
