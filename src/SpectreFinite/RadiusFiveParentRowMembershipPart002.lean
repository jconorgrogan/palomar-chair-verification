module

public import SpectreFinite.ParentOwnershipFinite

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem parentChunk_mem016 : ParentOwnership.parentRows016 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 16) (by decide)
theorem parentRow_mem0256 : ParentOwnership.parentRow0256 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 0) (by decide)
theorem parentRow_mem0257 : ParentOwnership.parentRow0257 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 1) (by decide)
theorem parentRow_mem0258 : ParentOwnership.parentRow0258 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 2) (by decide)
theorem parentRow_mem0259 : ParentOwnership.parentRow0259 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 3) (by decide)
theorem parentRow_mem0260 : ParentOwnership.parentRow0260 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 4) (by decide)
theorem parentRow_mem0261 : ParentOwnership.parentRow0261 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 5) (by decide)
theorem parentRow_mem0262 : ParentOwnership.parentRow0262 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 6) (by decide)
theorem parentRow_mem0263 : ParentOwnership.parentRow0263 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 7) (by decide)
theorem parentRow_mem0264 : ParentOwnership.parentRow0264 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 8) (by decide)
theorem parentRow_mem0265 : ParentOwnership.parentRow0265 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 9) (by decide)
theorem parentRow_mem0266 : ParentOwnership.parentRow0266 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 10) (by decide)
theorem parentRow_mem0267 : ParentOwnership.parentRow0267 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 11) (by decide)
theorem parentRow_mem0268 : ParentOwnership.parentRow0268 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 12) (by decide)
theorem parentRow_mem0269 : ParentOwnership.parentRow0269 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 13) (by decide)
theorem parentRow_mem0270 : ParentOwnership.parentRow0270 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 14) (by decide)
theorem parentRow_mem0271 : ParentOwnership.parentRow0271 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows016, parentChunk_mem016, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows016) (n := 15) (by decide)
theorem parentChunk_mem017 : ParentOwnership.parentRows017 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 17) (by decide)
theorem parentRow_mem0272 : ParentOwnership.parentRow0272 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 0) (by decide)
theorem parentRow_mem0273 : ParentOwnership.parentRow0273 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 1) (by decide)
theorem parentRow_mem0274 : ParentOwnership.parentRow0274 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 2) (by decide)
theorem parentRow_mem0275 : ParentOwnership.parentRow0275 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 3) (by decide)
theorem parentRow_mem0276 : ParentOwnership.parentRow0276 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 4) (by decide)
theorem parentRow_mem0277 : ParentOwnership.parentRow0277 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 5) (by decide)
theorem parentRow_mem0278 : ParentOwnership.parentRow0278 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 6) (by decide)
theorem parentRow_mem0279 : ParentOwnership.parentRow0279 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 7) (by decide)
theorem parentRow_mem0280 : ParentOwnership.parentRow0280 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 8) (by decide)
theorem parentRow_mem0281 : ParentOwnership.parentRow0281 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 9) (by decide)
theorem parentRow_mem0282 : ParentOwnership.parentRow0282 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 10) (by decide)
theorem parentRow_mem0283 : ParentOwnership.parentRow0283 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 11) (by decide)
theorem parentRow_mem0284 : ParentOwnership.parentRow0284 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 12) (by decide)
theorem parentRow_mem0285 : ParentOwnership.parentRow0285 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 13) (by decide)
theorem parentRow_mem0286 : ParentOwnership.parentRow0286 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 14) (by decide)
theorem parentRow_mem0287 : ParentOwnership.parentRow0287 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows017, parentChunk_mem017, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows017) (n := 15) (by decide)
theorem parentChunk_mem018 : ParentOwnership.parentRows018 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 18) (by decide)
theorem parentRow_mem0288 : ParentOwnership.parentRow0288 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 0) (by decide)
theorem parentRow_mem0289 : ParentOwnership.parentRow0289 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 1) (by decide)
theorem parentRow_mem0290 : ParentOwnership.parentRow0290 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 2) (by decide)
theorem parentRow_mem0291 : ParentOwnership.parentRow0291 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 3) (by decide)
theorem parentRow_mem0292 : ParentOwnership.parentRow0292 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 4) (by decide)
theorem parentRow_mem0293 : ParentOwnership.parentRow0293 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 5) (by decide)
theorem parentRow_mem0294 : ParentOwnership.parentRow0294 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 6) (by decide)
theorem parentRow_mem0295 : ParentOwnership.parentRow0295 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 7) (by decide)
theorem parentRow_mem0296 : ParentOwnership.parentRow0296 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 8) (by decide)
theorem parentRow_mem0297 : ParentOwnership.parentRow0297 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 9) (by decide)
theorem parentRow_mem0298 : ParentOwnership.parentRow0298 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 10) (by decide)
theorem parentRow_mem0299 : ParentOwnership.parentRow0299 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 11) (by decide)
theorem parentRow_mem0300 : ParentOwnership.parentRow0300 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 12) (by decide)
theorem parentRow_mem0301 : ParentOwnership.parentRow0301 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 13) (by decide)
theorem parentRow_mem0302 : ParentOwnership.parentRow0302 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 14) (by decide)
theorem parentRow_mem0303 : ParentOwnership.parentRow0303 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows018, parentChunk_mem018, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows018) (n := 15) (by decide)
theorem parentChunk_mem019 : ParentOwnership.parentRows019 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 19) (by decide)
theorem parentRow_mem0304 : ParentOwnership.parentRow0304 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 0) (by decide)
theorem parentRow_mem0305 : ParentOwnership.parentRow0305 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 1) (by decide)
theorem parentRow_mem0306 : ParentOwnership.parentRow0306 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 2) (by decide)
theorem parentRow_mem0307 : ParentOwnership.parentRow0307 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 3) (by decide)
theorem parentRow_mem0308 : ParentOwnership.parentRow0308 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 4) (by decide)
theorem parentRow_mem0309 : ParentOwnership.parentRow0309 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 5) (by decide)
theorem parentRow_mem0310 : ParentOwnership.parentRow0310 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 6) (by decide)
theorem parentRow_mem0311 : ParentOwnership.parentRow0311 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 7) (by decide)
theorem parentRow_mem0312 : ParentOwnership.parentRow0312 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 8) (by decide)
theorem parentRow_mem0313 : ParentOwnership.parentRow0313 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 9) (by decide)
theorem parentRow_mem0314 : ParentOwnership.parentRow0314 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 10) (by decide)
theorem parentRow_mem0315 : ParentOwnership.parentRow0315 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 11) (by decide)
theorem parentRow_mem0316 : ParentOwnership.parentRow0316 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 12) (by decide)
theorem parentRow_mem0317 : ParentOwnership.parentRow0317 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 13) (by decide)
theorem parentRow_mem0318 : ParentOwnership.parentRow0318 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 14) (by decide)
theorem parentRow_mem0319 : ParentOwnership.parentRow0319 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows019, parentChunk_mem019, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows019) (n := 15) (by decide)
theorem parentChunk_mem020 : ParentOwnership.parentRows020 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 20) (by decide)
theorem parentRow_mem0320 : ParentOwnership.parentRow0320 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 0) (by decide)
theorem parentRow_mem0321 : ParentOwnership.parentRow0321 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 1) (by decide)
theorem parentRow_mem0322 : ParentOwnership.parentRow0322 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 2) (by decide)
theorem parentRow_mem0323 : ParentOwnership.parentRow0323 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 3) (by decide)
theorem parentRow_mem0324 : ParentOwnership.parentRow0324 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 4) (by decide)
theorem parentRow_mem0325 : ParentOwnership.parentRow0325 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 5) (by decide)
theorem parentRow_mem0326 : ParentOwnership.parentRow0326 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 6) (by decide)
theorem parentRow_mem0327 : ParentOwnership.parentRow0327 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 7) (by decide)
theorem parentRow_mem0328 : ParentOwnership.parentRow0328 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 8) (by decide)
theorem parentRow_mem0329 : ParentOwnership.parentRow0329 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 9) (by decide)
theorem parentRow_mem0330 : ParentOwnership.parentRow0330 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 10) (by decide)
theorem parentRow_mem0331 : ParentOwnership.parentRow0331 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 11) (by decide)
theorem parentRow_mem0332 : ParentOwnership.parentRow0332 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 12) (by decide)
theorem parentRow_mem0333 : ParentOwnership.parentRow0333 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 13) (by decide)
theorem parentRow_mem0334 : ParentOwnership.parentRow0334 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 14) (by decide)
theorem parentRow_mem0335 : ParentOwnership.parentRow0335 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows020, parentChunk_mem020, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows020) (n := 15) (by decide)
theorem parentChunk_mem021 : ParentOwnership.parentRows021 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 21) (by decide)
theorem parentRow_mem0336 : ParentOwnership.parentRow0336 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 0) (by decide)
theorem parentRow_mem0337 : ParentOwnership.parentRow0337 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 1) (by decide)
theorem parentRow_mem0338 : ParentOwnership.parentRow0338 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 2) (by decide)
theorem parentRow_mem0339 : ParentOwnership.parentRow0339 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 3) (by decide)
theorem parentRow_mem0340 : ParentOwnership.parentRow0340 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 4) (by decide)
theorem parentRow_mem0341 : ParentOwnership.parentRow0341 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 5) (by decide)
theorem parentRow_mem0342 : ParentOwnership.parentRow0342 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 6) (by decide)
theorem parentRow_mem0343 : ParentOwnership.parentRow0343 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 7) (by decide)
theorem parentRow_mem0344 : ParentOwnership.parentRow0344 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 8) (by decide)
theorem parentRow_mem0345 : ParentOwnership.parentRow0345 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 9) (by decide)
theorem parentRow_mem0346 : ParentOwnership.parentRow0346 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 10) (by decide)
theorem parentRow_mem0347 : ParentOwnership.parentRow0347 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 11) (by decide)
theorem parentRow_mem0348 : ParentOwnership.parentRow0348 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 12) (by decide)
theorem parentRow_mem0349 : ParentOwnership.parentRow0349 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 13) (by decide)
theorem parentRow_mem0350 : ParentOwnership.parentRow0350 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 14) (by decide)
theorem parentRow_mem0351 : ParentOwnership.parentRow0351 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows021, parentChunk_mem021, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows021) (n := 15) (by decide)
theorem parentChunk_mem022 : ParentOwnership.parentRows022 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 22) (by decide)
theorem parentRow_mem0352 : ParentOwnership.parentRow0352 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 0) (by decide)
theorem parentRow_mem0353 : ParentOwnership.parentRow0353 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 1) (by decide)
theorem parentRow_mem0354 : ParentOwnership.parentRow0354 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 2) (by decide)
theorem parentRow_mem0355 : ParentOwnership.parentRow0355 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 3) (by decide)
theorem parentRow_mem0356 : ParentOwnership.parentRow0356 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 4) (by decide)
theorem parentRow_mem0357 : ParentOwnership.parentRow0357 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 5) (by decide)
theorem parentRow_mem0358 : ParentOwnership.parentRow0358 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 6) (by decide)
theorem parentRow_mem0359 : ParentOwnership.parentRow0359 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 7) (by decide)
theorem parentRow_mem0360 : ParentOwnership.parentRow0360 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 8) (by decide)
theorem parentRow_mem0361 : ParentOwnership.parentRow0361 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 9) (by decide)
theorem parentRow_mem0362 : ParentOwnership.parentRow0362 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 10) (by decide)
theorem parentRow_mem0363 : ParentOwnership.parentRow0363 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 11) (by decide)
theorem parentRow_mem0364 : ParentOwnership.parentRow0364 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 12) (by decide)
theorem parentRow_mem0365 : ParentOwnership.parentRow0365 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 13) (by decide)
theorem parentRow_mem0366 : ParentOwnership.parentRow0366 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 14) (by decide)
theorem parentRow_mem0367 : ParentOwnership.parentRow0367 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows022, parentChunk_mem022, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows022) (n := 15) (by decide)
theorem parentChunk_mem023 : ParentOwnership.parentRows023 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 23) (by decide)
theorem parentRow_mem0368 : ParentOwnership.parentRow0368 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 0) (by decide)
theorem parentRow_mem0369 : ParentOwnership.parentRow0369 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 1) (by decide)
theorem parentRow_mem0370 : ParentOwnership.parentRow0370 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 2) (by decide)
theorem parentRow_mem0371 : ParentOwnership.parentRow0371 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 3) (by decide)
theorem parentRow_mem0372 : ParentOwnership.parentRow0372 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 4) (by decide)
theorem parentRow_mem0373 : ParentOwnership.parentRow0373 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 5) (by decide)
theorem parentRow_mem0374 : ParentOwnership.parentRow0374 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 6) (by decide)
theorem parentRow_mem0375 : ParentOwnership.parentRow0375 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 7) (by decide)
theorem parentRow_mem0376 : ParentOwnership.parentRow0376 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 8) (by decide)
theorem parentRow_mem0377 : ParentOwnership.parentRow0377 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 9) (by decide)
theorem parentRow_mem0378 : ParentOwnership.parentRow0378 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 10) (by decide)
theorem parentRow_mem0379 : ParentOwnership.parentRow0379 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 11) (by decide)
theorem parentRow_mem0380 : ParentOwnership.parentRow0380 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 12) (by decide)
theorem parentRow_mem0381 : ParentOwnership.parentRow0381 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 13) (by decide)
theorem parentRow_mem0382 : ParentOwnership.parentRow0382 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 14) (by decide)
theorem parentRow_mem0383 : ParentOwnership.parentRow0383 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows023, parentChunk_mem023, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows023) (n := 15) (by decide)

end SpectreFinite.HexSearch.RadiusFiveParentBinding
