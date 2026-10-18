module

public import SpectreFinite.ParentOwnershipFinite

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem parentChunk_mem024 : ParentOwnership.parentRows024 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 24) (by decide)
theorem parentRow_mem0384 : ParentOwnership.parentRow0384 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 0) (by decide)
theorem parentRow_mem0385 : ParentOwnership.parentRow0385 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 1) (by decide)
theorem parentRow_mem0386 : ParentOwnership.parentRow0386 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 2) (by decide)
theorem parentRow_mem0387 : ParentOwnership.parentRow0387 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 3) (by decide)
theorem parentRow_mem0388 : ParentOwnership.parentRow0388 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 4) (by decide)
theorem parentRow_mem0389 : ParentOwnership.parentRow0389 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 5) (by decide)
theorem parentRow_mem0390 : ParentOwnership.parentRow0390 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 6) (by decide)
theorem parentRow_mem0391 : ParentOwnership.parentRow0391 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 7) (by decide)
theorem parentRow_mem0392 : ParentOwnership.parentRow0392 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 8) (by decide)
theorem parentRow_mem0393 : ParentOwnership.parentRow0393 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 9) (by decide)
theorem parentRow_mem0394 : ParentOwnership.parentRow0394 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 10) (by decide)
theorem parentRow_mem0395 : ParentOwnership.parentRow0395 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 11) (by decide)
theorem parentRow_mem0396 : ParentOwnership.parentRow0396 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 12) (by decide)
theorem parentRow_mem0397 : ParentOwnership.parentRow0397 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 13) (by decide)
theorem parentRow_mem0398 : ParentOwnership.parentRow0398 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 14) (by decide)
theorem parentRow_mem0399 : ParentOwnership.parentRow0399 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows024, parentChunk_mem024, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows024) (n := 15) (by decide)
theorem parentChunk_mem025 : ParentOwnership.parentRows025 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 25) (by decide)
theorem parentRow_mem0400 : ParentOwnership.parentRow0400 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 0) (by decide)
theorem parentRow_mem0401 : ParentOwnership.parentRow0401 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 1) (by decide)
theorem parentRow_mem0402 : ParentOwnership.parentRow0402 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 2) (by decide)
theorem parentRow_mem0403 : ParentOwnership.parentRow0403 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 3) (by decide)
theorem parentRow_mem0404 : ParentOwnership.parentRow0404 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 4) (by decide)
theorem parentRow_mem0405 : ParentOwnership.parentRow0405 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 5) (by decide)
theorem parentRow_mem0406 : ParentOwnership.parentRow0406 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 6) (by decide)
theorem parentRow_mem0407 : ParentOwnership.parentRow0407 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 7) (by decide)
theorem parentRow_mem0408 : ParentOwnership.parentRow0408 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 8) (by decide)
theorem parentRow_mem0409 : ParentOwnership.parentRow0409 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 9) (by decide)
theorem parentRow_mem0410 : ParentOwnership.parentRow0410 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 10) (by decide)
theorem parentRow_mem0411 : ParentOwnership.parentRow0411 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 11) (by decide)
theorem parentRow_mem0412 : ParentOwnership.parentRow0412 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 12) (by decide)
theorem parentRow_mem0413 : ParentOwnership.parentRow0413 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 13) (by decide)
theorem parentRow_mem0414 : ParentOwnership.parentRow0414 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 14) (by decide)
theorem parentRow_mem0415 : ParentOwnership.parentRow0415 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows025, parentChunk_mem025, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows025) (n := 15) (by decide)
theorem parentChunk_mem026 : ParentOwnership.parentRows026 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 26) (by decide)
theorem parentRow_mem0416 : ParentOwnership.parentRow0416 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 0) (by decide)
theorem parentRow_mem0417 : ParentOwnership.parentRow0417 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 1) (by decide)
theorem parentRow_mem0418 : ParentOwnership.parentRow0418 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 2) (by decide)
theorem parentRow_mem0419 : ParentOwnership.parentRow0419 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 3) (by decide)
theorem parentRow_mem0420 : ParentOwnership.parentRow0420 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 4) (by decide)
theorem parentRow_mem0421 : ParentOwnership.parentRow0421 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 5) (by decide)
theorem parentRow_mem0422 : ParentOwnership.parentRow0422 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 6) (by decide)
theorem parentRow_mem0423 : ParentOwnership.parentRow0423 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 7) (by decide)
theorem parentRow_mem0424 : ParentOwnership.parentRow0424 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 8) (by decide)
theorem parentRow_mem0425 : ParentOwnership.parentRow0425 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 9) (by decide)
theorem parentRow_mem0426 : ParentOwnership.parentRow0426 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 10) (by decide)
theorem parentRow_mem0427 : ParentOwnership.parentRow0427 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 11) (by decide)
theorem parentRow_mem0428 : ParentOwnership.parentRow0428 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 12) (by decide)
theorem parentRow_mem0429 : ParentOwnership.parentRow0429 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 13) (by decide)
theorem parentRow_mem0430 : ParentOwnership.parentRow0430 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 14) (by decide)
theorem parentRow_mem0431 : ParentOwnership.parentRow0431 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows026, parentChunk_mem026, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows026) (n := 15) (by decide)
theorem parentChunk_mem027 : ParentOwnership.parentRows027 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 27) (by decide)
theorem parentRow_mem0432 : ParentOwnership.parentRow0432 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 0) (by decide)
theorem parentRow_mem0433 : ParentOwnership.parentRow0433 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 1) (by decide)
theorem parentRow_mem0434 : ParentOwnership.parentRow0434 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 2) (by decide)
theorem parentRow_mem0435 : ParentOwnership.parentRow0435 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 3) (by decide)
theorem parentRow_mem0436 : ParentOwnership.parentRow0436 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 4) (by decide)
theorem parentRow_mem0437 : ParentOwnership.parentRow0437 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 5) (by decide)
theorem parentRow_mem0438 : ParentOwnership.parentRow0438 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 6) (by decide)
theorem parentRow_mem0439 : ParentOwnership.parentRow0439 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 7) (by decide)
theorem parentRow_mem0440 : ParentOwnership.parentRow0440 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 8) (by decide)
theorem parentRow_mem0441 : ParentOwnership.parentRow0441 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 9) (by decide)
theorem parentRow_mem0442 : ParentOwnership.parentRow0442 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 10) (by decide)
theorem parentRow_mem0443 : ParentOwnership.parentRow0443 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 11) (by decide)
theorem parentRow_mem0444 : ParentOwnership.parentRow0444 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 12) (by decide)
theorem parentRow_mem0445 : ParentOwnership.parentRow0445 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 13) (by decide)
theorem parentRow_mem0446 : ParentOwnership.parentRow0446 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 14) (by decide)
theorem parentRow_mem0447 : ParentOwnership.parentRow0447 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows027, parentChunk_mem027, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows027) (n := 15) (by decide)
theorem parentChunk_mem028 : ParentOwnership.parentRows028 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 28) (by decide)
theorem parentRow_mem0448 : ParentOwnership.parentRow0448 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 0) (by decide)
theorem parentRow_mem0449 : ParentOwnership.parentRow0449 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 1) (by decide)
theorem parentRow_mem0450 : ParentOwnership.parentRow0450 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 2) (by decide)
theorem parentRow_mem0451 : ParentOwnership.parentRow0451 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 3) (by decide)
theorem parentRow_mem0452 : ParentOwnership.parentRow0452 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 4) (by decide)
theorem parentRow_mem0453 : ParentOwnership.parentRow0453 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 5) (by decide)
theorem parentRow_mem0454 : ParentOwnership.parentRow0454 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 6) (by decide)
theorem parentRow_mem0455 : ParentOwnership.parentRow0455 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 7) (by decide)
theorem parentRow_mem0456 : ParentOwnership.parentRow0456 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 8) (by decide)
theorem parentRow_mem0457 : ParentOwnership.parentRow0457 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 9) (by decide)
theorem parentRow_mem0458 : ParentOwnership.parentRow0458 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 10) (by decide)
theorem parentRow_mem0459 : ParentOwnership.parentRow0459 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 11) (by decide)
theorem parentRow_mem0460 : ParentOwnership.parentRow0460 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 12) (by decide)
theorem parentRow_mem0461 : ParentOwnership.parentRow0461 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 13) (by decide)
theorem parentRow_mem0462 : ParentOwnership.parentRow0462 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 14) (by decide)
theorem parentRow_mem0463 : ParentOwnership.parentRow0463 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows028, parentChunk_mem028, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows028) (n := 15) (by decide)
theorem parentChunk_mem029 : ParentOwnership.parentRows029 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 29) (by decide)
theorem parentRow_mem0464 : ParentOwnership.parentRow0464 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 0) (by decide)
theorem parentRow_mem0465 : ParentOwnership.parentRow0465 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 1) (by decide)
theorem parentRow_mem0466 : ParentOwnership.parentRow0466 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 2) (by decide)
theorem parentRow_mem0467 : ParentOwnership.parentRow0467 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 3) (by decide)
theorem parentRow_mem0468 : ParentOwnership.parentRow0468 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 4) (by decide)
theorem parentRow_mem0469 : ParentOwnership.parentRow0469 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 5) (by decide)
theorem parentRow_mem0470 : ParentOwnership.parentRow0470 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 6) (by decide)
theorem parentRow_mem0471 : ParentOwnership.parentRow0471 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 7) (by decide)
theorem parentRow_mem0472 : ParentOwnership.parentRow0472 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 8) (by decide)
theorem parentRow_mem0473 : ParentOwnership.parentRow0473 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 9) (by decide)
theorem parentRow_mem0474 : ParentOwnership.parentRow0474 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 10) (by decide)
theorem parentRow_mem0475 : ParentOwnership.parentRow0475 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 11) (by decide)
theorem parentRow_mem0476 : ParentOwnership.parentRow0476 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 12) (by decide)
theorem parentRow_mem0477 : ParentOwnership.parentRow0477 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 13) (by decide)
theorem parentRow_mem0478 : ParentOwnership.parentRow0478 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 14) (by decide)
theorem parentRow_mem0479 : ParentOwnership.parentRow0479 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows029, parentChunk_mem029, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows029) (n := 15) (by decide)
theorem parentChunk_mem030 : ParentOwnership.parentRows030 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 30) (by decide)
theorem parentRow_mem0480 : ParentOwnership.parentRow0480 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 0) (by decide)
theorem parentRow_mem0481 : ParentOwnership.parentRow0481 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 1) (by decide)
theorem parentRow_mem0482 : ParentOwnership.parentRow0482 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 2) (by decide)
theorem parentRow_mem0483 : ParentOwnership.parentRow0483 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 3) (by decide)
theorem parentRow_mem0484 : ParentOwnership.parentRow0484 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 4) (by decide)
theorem parentRow_mem0485 : ParentOwnership.parentRow0485 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 5) (by decide)
theorem parentRow_mem0486 : ParentOwnership.parentRow0486 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 6) (by decide)
theorem parentRow_mem0487 : ParentOwnership.parentRow0487 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 7) (by decide)
theorem parentRow_mem0488 : ParentOwnership.parentRow0488 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 8) (by decide)
theorem parentRow_mem0489 : ParentOwnership.parentRow0489 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 9) (by decide)
theorem parentRow_mem0490 : ParentOwnership.parentRow0490 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 10) (by decide)
theorem parentRow_mem0491 : ParentOwnership.parentRow0491 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 11) (by decide)
theorem parentRow_mem0492 : ParentOwnership.parentRow0492 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 12) (by decide)
theorem parentRow_mem0493 : ParentOwnership.parentRow0493 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 13) (by decide)
theorem parentRow_mem0494 : ParentOwnership.parentRow0494 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 14) (by decide)
theorem parentRow_mem0495 : ParentOwnership.parentRow0495 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows030, parentChunk_mem030, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows030) (n := 15) (by decide)
theorem parentChunk_mem031 : ParentOwnership.parentRows031 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 31) (by decide)
theorem parentRow_mem0496 : ParentOwnership.parentRow0496 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 0) (by decide)
theorem parentRow_mem0497 : ParentOwnership.parentRow0497 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 1) (by decide)
theorem parentRow_mem0498 : ParentOwnership.parentRow0498 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 2) (by decide)
theorem parentRow_mem0499 : ParentOwnership.parentRow0499 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 3) (by decide)
theorem parentRow_mem0500 : ParentOwnership.parentRow0500 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 4) (by decide)
theorem parentRow_mem0501 : ParentOwnership.parentRow0501 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 5) (by decide)
theorem parentRow_mem0502 : ParentOwnership.parentRow0502 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 6) (by decide)
theorem parentRow_mem0503 : ParentOwnership.parentRow0503 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 7) (by decide)
theorem parentRow_mem0504 : ParentOwnership.parentRow0504 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 8) (by decide)
theorem parentRow_mem0505 : ParentOwnership.parentRow0505 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 9) (by decide)
theorem parentRow_mem0506 : ParentOwnership.parentRow0506 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 10) (by decide)
theorem parentRow_mem0507 : ParentOwnership.parentRow0507 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 11) (by decide)
theorem parentRow_mem0508 : ParentOwnership.parentRow0508 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 12) (by decide)
theorem parentRow_mem0509 : ParentOwnership.parentRow0509 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 13) (by decide)
theorem parentRow_mem0510 : ParentOwnership.parentRow0510 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 14) (by decide)
theorem parentRow_mem0511 : ParentOwnership.parentRow0511 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows031, parentChunk_mem031, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows031) (n := 15) (by decide)

end SpectreFinite.HexSearch.RadiusFiveParentBinding
