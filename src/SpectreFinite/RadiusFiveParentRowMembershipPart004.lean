module

public import SpectreFinite.ParentOwnershipFinite

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem parentChunk_mem032 : ParentOwnership.parentRows032 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 32) (by decide)
theorem parentRow_mem0512 : ParentOwnership.parentRow0512 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 0) (by decide)
theorem parentRow_mem0513 : ParentOwnership.parentRow0513 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 1) (by decide)
theorem parentRow_mem0514 : ParentOwnership.parentRow0514 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 2) (by decide)
theorem parentRow_mem0515 : ParentOwnership.parentRow0515 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 3) (by decide)
theorem parentRow_mem0516 : ParentOwnership.parentRow0516 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 4) (by decide)
theorem parentRow_mem0517 : ParentOwnership.parentRow0517 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 5) (by decide)
theorem parentRow_mem0518 : ParentOwnership.parentRow0518 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 6) (by decide)
theorem parentRow_mem0519 : ParentOwnership.parentRow0519 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 7) (by decide)
theorem parentRow_mem0520 : ParentOwnership.parentRow0520 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 8) (by decide)
theorem parentRow_mem0521 : ParentOwnership.parentRow0521 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 9) (by decide)
theorem parentRow_mem0522 : ParentOwnership.parentRow0522 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 10) (by decide)
theorem parentRow_mem0523 : ParentOwnership.parentRow0523 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 11) (by decide)
theorem parentRow_mem0524 : ParentOwnership.parentRow0524 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 12) (by decide)
theorem parentRow_mem0525 : ParentOwnership.parentRow0525 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 13) (by decide)
theorem parentRow_mem0526 : ParentOwnership.parentRow0526 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 14) (by decide)
theorem parentRow_mem0527 : ParentOwnership.parentRow0527 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows032, parentChunk_mem032, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows032) (n := 15) (by decide)
theorem parentChunk_mem033 : ParentOwnership.parentRows033 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 33) (by decide)
theorem parentRow_mem0528 : ParentOwnership.parentRow0528 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 0) (by decide)
theorem parentRow_mem0529 : ParentOwnership.parentRow0529 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 1) (by decide)
theorem parentRow_mem0530 : ParentOwnership.parentRow0530 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 2) (by decide)
theorem parentRow_mem0531 : ParentOwnership.parentRow0531 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 3) (by decide)
theorem parentRow_mem0532 : ParentOwnership.parentRow0532 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 4) (by decide)
theorem parentRow_mem0533 : ParentOwnership.parentRow0533 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 5) (by decide)
theorem parentRow_mem0534 : ParentOwnership.parentRow0534 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 6) (by decide)
theorem parentRow_mem0535 : ParentOwnership.parentRow0535 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 7) (by decide)
theorem parentRow_mem0536 : ParentOwnership.parentRow0536 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 8) (by decide)
theorem parentRow_mem0537 : ParentOwnership.parentRow0537 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 9) (by decide)
theorem parentRow_mem0538 : ParentOwnership.parentRow0538 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 10) (by decide)
theorem parentRow_mem0539 : ParentOwnership.parentRow0539 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 11) (by decide)
theorem parentRow_mem0540 : ParentOwnership.parentRow0540 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 12) (by decide)
theorem parentRow_mem0541 : ParentOwnership.parentRow0541 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 13) (by decide)
theorem parentRow_mem0542 : ParentOwnership.parentRow0542 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 14) (by decide)
theorem parentRow_mem0543 : ParentOwnership.parentRow0543 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows033, parentChunk_mem033, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows033) (n := 15) (by decide)
theorem parentChunk_mem034 : ParentOwnership.parentRows034 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 34) (by decide)
theorem parentRow_mem0544 : ParentOwnership.parentRow0544 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 0) (by decide)
theorem parentRow_mem0545 : ParentOwnership.parentRow0545 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 1) (by decide)
theorem parentRow_mem0546 : ParentOwnership.parentRow0546 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 2) (by decide)
theorem parentRow_mem0547 : ParentOwnership.parentRow0547 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 3) (by decide)
theorem parentRow_mem0548 : ParentOwnership.parentRow0548 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 4) (by decide)
theorem parentRow_mem0549 : ParentOwnership.parentRow0549 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 5) (by decide)
theorem parentRow_mem0550 : ParentOwnership.parentRow0550 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 6) (by decide)
theorem parentRow_mem0551 : ParentOwnership.parentRow0551 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 7) (by decide)
theorem parentRow_mem0552 : ParentOwnership.parentRow0552 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 8) (by decide)
theorem parentRow_mem0553 : ParentOwnership.parentRow0553 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 9) (by decide)
theorem parentRow_mem0554 : ParentOwnership.parentRow0554 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 10) (by decide)
theorem parentRow_mem0555 : ParentOwnership.parentRow0555 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 11) (by decide)
theorem parentRow_mem0556 : ParentOwnership.parentRow0556 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 12) (by decide)
theorem parentRow_mem0557 : ParentOwnership.parentRow0557 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 13) (by decide)
theorem parentRow_mem0558 : ParentOwnership.parentRow0558 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 14) (by decide)
theorem parentRow_mem0559 : ParentOwnership.parentRow0559 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows034, parentChunk_mem034, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows034) (n := 15) (by decide)
theorem parentChunk_mem035 : ParentOwnership.parentRows035 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 35) (by decide)
theorem parentRow_mem0560 : ParentOwnership.parentRow0560 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 0) (by decide)
theorem parentRow_mem0561 : ParentOwnership.parentRow0561 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 1) (by decide)
theorem parentRow_mem0562 : ParentOwnership.parentRow0562 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 2) (by decide)
theorem parentRow_mem0563 : ParentOwnership.parentRow0563 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 3) (by decide)
theorem parentRow_mem0564 : ParentOwnership.parentRow0564 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 4) (by decide)
theorem parentRow_mem0565 : ParentOwnership.parentRow0565 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 5) (by decide)
theorem parentRow_mem0566 : ParentOwnership.parentRow0566 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 6) (by decide)
theorem parentRow_mem0567 : ParentOwnership.parentRow0567 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 7) (by decide)
theorem parentRow_mem0568 : ParentOwnership.parentRow0568 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 8) (by decide)
theorem parentRow_mem0569 : ParentOwnership.parentRow0569 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 9) (by decide)
theorem parentRow_mem0570 : ParentOwnership.parentRow0570 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 10) (by decide)
theorem parentRow_mem0571 : ParentOwnership.parentRow0571 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 11) (by decide)
theorem parentRow_mem0572 : ParentOwnership.parentRow0572 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 12) (by decide)
theorem parentRow_mem0573 : ParentOwnership.parentRow0573 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 13) (by decide)
theorem parentRow_mem0574 : ParentOwnership.parentRow0574 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 14) (by decide)
theorem parentRow_mem0575 : ParentOwnership.parentRow0575 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows035, parentChunk_mem035, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows035) (n := 15) (by decide)
theorem parentChunk_mem036 : ParentOwnership.parentRows036 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 36) (by decide)
theorem parentRow_mem0576 : ParentOwnership.parentRow0576 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 0) (by decide)
theorem parentRow_mem0577 : ParentOwnership.parentRow0577 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 1) (by decide)
theorem parentRow_mem0578 : ParentOwnership.parentRow0578 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 2) (by decide)
theorem parentRow_mem0579 : ParentOwnership.parentRow0579 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 3) (by decide)
theorem parentRow_mem0580 : ParentOwnership.parentRow0580 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 4) (by decide)
theorem parentRow_mem0581 : ParentOwnership.parentRow0581 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 5) (by decide)
theorem parentRow_mem0582 : ParentOwnership.parentRow0582 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 6) (by decide)
theorem parentRow_mem0583 : ParentOwnership.parentRow0583 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 7) (by decide)
theorem parentRow_mem0584 : ParentOwnership.parentRow0584 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 8) (by decide)
theorem parentRow_mem0585 : ParentOwnership.parentRow0585 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 9) (by decide)
theorem parentRow_mem0586 : ParentOwnership.parentRow0586 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 10) (by decide)
theorem parentRow_mem0587 : ParentOwnership.parentRow0587 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 11) (by decide)
theorem parentRow_mem0588 : ParentOwnership.parentRow0588 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 12) (by decide)
theorem parentRow_mem0589 : ParentOwnership.parentRow0589 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 13) (by decide)
theorem parentRow_mem0590 : ParentOwnership.parentRow0590 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 14) (by decide)
theorem parentRow_mem0591 : ParentOwnership.parentRow0591 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows036, parentChunk_mem036, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows036) (n := 15) (by decide)
theorem parentChunk_mem037 : ParentOwnership.parentRows037 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 37) (by decide)
theorem parentRow_mem0592 : ParentOwnership.parentRow0592 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 0) (by decide)
theorem parentRow_mem0593 : ParentOwnership.parentRow0593 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 1) (by decide)
theorem parentRow_mem0594 : ParentOwnership.parentRow0594 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 2) (by decide)
theorem parentRow_mem0595 : ParentOwnership.parentRow0595 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 3) (by decide)
theorem parentRow_mem0596 : ParentOwnership.parentRow0596 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 4) (by decide)
theorem parentRow_mem0597 : ParentOwnership.parentRow0597 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 5) (by decide)
theorem parentRow_mem0598 : ParentOwnership.parentRow0598 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 6) (by decide)
theorem parentRow_mem0599 : ParentOwnership.parentRow0599 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 7) (by decide)
theorem parentRow_mem0600 : ParentOwnership.parentRow0600 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 8) (by decide)
theorem parentRow_mem0601 : ParentOwnership.parentRow0601 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 9) (by decide)
theorem parentRow_mem0602 : ParentOwnership.parentRow0602 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 10) (by decide)
theorem parentRow_mem0603 : ParentOwnership.parentRow0603 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 11) (by decide)
theorem parentRow_mem0604 : ParentOwnership.parentRow0604 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 12) (by decide)
theorem parentRow_mem0605 : ParentOwnership.parentRow0605 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 13) (by decide)
theorem parentRow_mem0606 : ParentOwnership.parentRow0606 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 14) (by decide)
theorem parentRow_mem0607 : ParentOwnership.parentRow0607 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows037, parentChunk_mem037, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows037) (n := 15) (by decide)
theorem parentChunk_mem038 : ParentOwnership.parentRows038 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 38) (by decide)
theorem parentRow_mem0608 : ParentOwnership.parentRow0608 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 0) (by decide)
theorem parentRow_mem0609 : ParentOwnership.parentRow0609 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 1) (by decide)
theorem parentRow_mem0610 : ParentOwnership.parentRow0610 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 2) (by decide)
theorem parentRow_mem0611 : ParentOwnership.parentRow0611 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 3) (by decide)
theorem parentRow_mem0612 : ParentOwnership.parentRow0612 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 4) (by decide)
theorem parentRow_mem0613 : ParentOwnership.parentRow0613 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 5) (by decide)
theorem parentRow_mem0614 : ParentOwnership.parentRow0614 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 6) (by decide)
theorem parentRow_mem0615 : ParentOwnership.parentRow0615 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 7) (by decide)
theorem parentRow_mem0616 : ParentOwnership.parentRow0616 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 8) (by decide)
theorem parentRow_mem0617 : ParentOwnership.parentRow0617 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 9) (by decide)
theorem parentRow_mem0618 : ParentOwnership.parentRow0618 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 10) (by decide)
theorem parentRow_mem0619 : ParentOwnership.parentRow0619 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 11) (by decide)
theorem parentRow_mem0620 : ParentOwnership.parentRow0620 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 12) (by decide)
theorem parentRow_mem0621 : ParentOwnership.parentRow0621 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 13) (by decide)
theorem parentRow_mem0622 : ParentOwnership.parentRow0622 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 14) (by decide)
theorem parentRow_mem0623 : ParentOwnership.parentRow0623 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows038, parentChunk_mem038, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows038) (n := 15) (by decide)
theorem parentChunk_mem039 : ParentOwnership.parentRows039 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 39) (by decide)
theorem parentRow_mem0624 : ParentOwnership.parentRow0624 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 0) (by decide)
theorem parentRow_mem0625 : ParentOwnership.parentRow0625 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 1) (by decide)
theorem parentRow_mem0626 : ParentOwnership.parentRow0626 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 2) (by decide)
theorem parentRow_mem0627 : ParentOwnership.parentRow0627 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 3) (by decide)
theorem parentRow_mem0628 : ParentOwnership.parentRow0628 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 4) (by decide)
theorem parentRow_mem0629 : ParentOwnership.parentRow0629 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 5) (by decide)
theorem parentRow_mem0630 : ParentOwnership.parentRow0630 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 6) (by decide)
theorem parentRow_mem0631 : ParentOwnership.parentRow0631 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 7) (by decide)
theorem parentRow_mem0632 : ParentOwnership.parentRow0632 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 8) (by decide)
theorem parentRow_mem0633 : ParentOwnership.parentRow0633 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 9) (by decide)
theorem parentRow_mem0634 : ParentOwnership.parentRow0634 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 10) (by decide)
theorem parentRow_mem0635 : ParentOwnership.parentRow0635 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 11) (by decide)
theorem parentRow_mem0636 : ParentOwnership.parentRow0636 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 12) (by decide)
theorem parentRow_mem0637 : ParentOwnership.parentRow0637 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 13) (by decide)
theorem parentRow_mem0638 : ParentOwnership.parentRow0638 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 14) (by decide)
theorem parentRow_mem0639 : ParentOwnership.parentRow0639 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows039, parentChunk_mem039, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows039) (n := 15) (by decide)

end SpectreFinite.HexSearch.RadiusFiveParentBinding
