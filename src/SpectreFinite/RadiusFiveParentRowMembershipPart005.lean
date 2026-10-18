module

public import SpectreFinite.ParentOwnershipFinite

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem parentChunk_mem040 : ParentOwnership.parentRows040 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 40) (by decide)
theorem parentRow_mem0640 : ParentOwnership.parentRow0640 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 0) (by decide)
theorem parentRow_mem0641 : ParentOwnership.parentRow0641 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 1) (by decide)
theorem parentRow_mem0642 : ParentOwnership.parentRow0642 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 2) (by decide)
theorem parentRow_mem0643 : ParentOwnership.parentRow0643 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 3) (by decide)
theorem parentRow_mem0644 : ParentOwnership.parentRow0644 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 4) (by decide)
theorem parentRow_mem0645 : ParentOwnership.parentRow0645 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 5) (by decide)
theorem parentRow_mem0646 : ParentOwnership.parentRow0646 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 6) (by decide)
theorem parentRow_mem0647 : ParentOwnership.parentRow0647 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 7) (by decide)
theorem parentRow_mem0648 : ParentOwnership.parentRow0648 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 8) (by decide)
theorem parentRow_mem0649 : ParentOwnership.parentRow0649 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 9) (by decide)
theorem parentRow_mem0650 : ParentOwnership.parentRow0650 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 10) (by decide)
theorem parentRow_mem0651 : ParentOwnership.parentRow0651 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 11) (by decide)
theorem parentRow_mem0652 : ParentOwnership.parentRow0652 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 12) (by decide)
theorem parentRow_mem0653 : ParentOwnership.parentRow0653 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 13) (by decide)
theorem parentRow_mem0654 : ParentOwnership.parentRow0654 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 14) (by decide)
theorem parentRow_mem0655 : ParentOwnership.parentRow0655 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows040, parentChunk_mem040, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows040) (n := 15) (by decide)
theorem parentChunk_mem041 : ParentOwnership.parentRows041 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 41) (by decide)
theorem parentRow_mem0656 : ParentOwnership.parentRow0656 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 0) (by decide)
theorem parentRow_mem0657 : ParentOwnership.parentRow0657 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 1) (by decide)
theorem parentRow_mem0658 : ParentOwnership.parentRow0658 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 2) (by decide)
theorem parentRow_mem0659 : ParentOwnership.parentRow0659 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 3) (by decide)
theorem parentRow_mem0660 : ParentOwnership.parentRow0660 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 4) (by decide)
theorem parentRow_mem0661 : ParentOwnership.parentRow0661 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 5) (by decide)
theorem parentRow_mem0662 : ParentOwnership.parentRow0662 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 6) (by decide)
theorem parentRow_mem0663 : ParentOwnership.parentRow0663 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 7) (by decide)
theorem parentRow_mem0664 : ParentOwnership.parentRow0664 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 8) (by decide)
theorem parentRow_mem0665 : ParentOwnership.parentRow0665 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 9) (by decide)
theorem parentRow_mem0666 : ParentOwnership.parentRow0666 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 10) (by decide)
theorem parentRow_mem0667 : ParentOwnership.parentRow0667 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 11) (by decide)
theorem parentRow_mem0668 : ParentOwnership.parentRow0668 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 12) (by decide)
theorem parentRow_mem0669 : ParentOwnership.parentRow0669 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 13) (by decide)
theorem parentRow_mem0670 : ParentOwnership.parentRow0670 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 14) (by decide)
theorem parentRow_mem0671 : ParentOwnership.parentRow0671 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows041, parentChunk_mem041, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows041) (n := 15) (by decide)
theorem parentChunk_mem042 : ParentOwnership.parentRows042 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 42) (by decide)
theorem parentRow_mem0672 : ParentOwnership.parentRow0672 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 0) (by decide)
theorem parentRow_mem0673 : ParentOwnership.parentRow0673 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 1) (by decide)
theorem parentRow_mem0674 : ParentOwnership.parentRow0674 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 2) (by decide)
theorem parentRow_mem0675 : ParentOwnership.parentRow0675 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 3) (by decide)
theorem parentRow_mem0676 : ParentOwnership.parentRow0676 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 4) (by decide)
theorem parentRow_mem0677 : ParentOwnership.parentRow0677 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 5) (by decide)
theorem parentRow_mem0678 : ParentOwnership.parentRow0678 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 6) (by decide)
theorem parentRow_mem0679 : ParentOwnership.parentRow0679 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 7) (by decide)
theorem parentRow_mem0680 : ParentOwnership.parentRow0680 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 8) (by decide)
theorem parentRow_mem0681 : ParentOwnership.parentRow0681 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 9) (by decide)
theorem parentRow_mem0682 : ParentOwnership.parentRow0682 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 10) (by decide)
theorem parentRow_mem0683 : ParentOwnership.parentRow0683 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 11) (by decide)
theorem parentRow_mem0684 : ParentOwnership.parentRow0684 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 12) (by decide)
theorem parentRow_mem0685 : ParentOwnership.parentRow0685 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 13) (by decide)
theorem parentRow_mem0686 : ParentOwnership.parentRow0686 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 14) (by decide)
theorem parentRow_mem0687 : ParentOwnership.parentRow0687 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows042, parentChunk_mem042, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows042) (n := 15) (by decide)
theorem parentChunk_mem043 : ParentOwnership.parentRows043 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 43) (by decide)
theorem parentRow_mem0688 : ParentOwnership.parentRow0688 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 0) (by decide)
theorem parentRow_mem0689 : ParentOwnership.parentRow0689 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 1) (by decide)
theorem parentRow_mem0690 : ParentOwnership.parentRow0690 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 2) (by decide)
theorem parentRow_mem0691 : ParentOwnership.parentRow0691 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 3) (by decide)
theorem parentRow_mem0692 : ParentOwnership.parentRow0692 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 4) (by decide)
theorem parentRow_mem0693 : ParentOwnership.parentRow0693 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 5) (by decide)
theorem parentRow_mem0694 : ParentOwnership.parentRow0694 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 6) (by decide)
theorem parentRow_mem0695 : ParentOwnership.parentRow0695 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 7) (by decide)
theorem parentRow_mem0696 : ParentOwnership.parentRow0696 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 8) (by decide)
theorem parentRow_mem0697 : ParentOwnership.parentRow0697 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 9) (by decide)
theorem parentRow_mem0698 : ParentOwnership.parentRow0698 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 10) (by decide)
theorem parentRow_mem0699 : ParentOwnership.parentRow0699 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 11) (by decide)
theorem parentRow_mem0700 : ParentOwnership.parentRow0700 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 12) (by decide)
theorem parentRow_mem0701 : ParentOwnership.parentRow0701 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 13) (by decide)
theorem parentRow_mem0702 : ParentOwnership.parentRow0702 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 14) (by decide)
theorem parentRow_mem0703 : ParentOwnership.parentRow0703 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows043, parentChunk_mem043, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows043) (n := 15) (by decide)
theorem parentChunk_mem044 : ParentOwnership.parentRows044 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 44) (by decide)
theorem parentRow_mem0704 : ParentOwnership.parentRow0704 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 0) (by decide)
theorem parentRow_mem0705 : ParentOwnership.parentRow0705 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 1) (by decide)
theorem parentRow_mem0706 : ParentOwnership.parentRow0706 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 2) (by decide)
theorem parentRow_mem0707 : ParentOwnership.parentRow0707 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 3) (by decide)
theorem parentRow_mem0708 : ParentOwnership.parentRow0708 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 4) (by decide)
theorem parentRow_mem0709 : ParentOwnership.parentRow0709 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 5) (by decide)
theorem parentRow_mem0710 : ParentOwnership.parentRow0710 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 6) (by decide)
theorem parentRow_mem0711 : ParentOwnership.parentRow0711 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 7) (by decide)
theorem parentRow_mem0712 : ParentOwnership.parentRow0712 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 8) (by decide)
theorem parentRow_mem0713 : ParentOwnership.parentRow0713 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 9) (by decide)
theorem parentRow_mem0714 : ParentOwnership.parentRow0714 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 10) (by decide)
theorem parentRow_mem0715 : ParentOwnership.parentRow0715 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 11) (by decide)
theorem parentRow_mem0716 : ParentOwnership.parentRow0716 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 12) (by decide)
theorem parentRow_mem0717 : ParentOwnership.parentRow0717 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 13) (by decide)
theorem parentRow_mem0718 : ParentOwnership.parentRow0718 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 14) (by decide)
theorem parentRow_mem0719 : ParentOwnership.parentRow0719 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows044, parentChunk_mem044, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows044) (n := 15) (by decide)
theorem parentChunk_mem045 : ParentOwnership.parentRows045 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 45) (by decide)
theorem parentRow_mem0720 : ParentOwnership.parentRow0720 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 0) (by decide)
theorem parentRow_mem0721 : ParentOwnership.parentRow0721 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 1) (by decide)
theorem parentRow_mem0722 : ParentOwnership.parentRow0722 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 2) (by decide)
theorem parentRow_mem0723 : ParentOwnership.parentRow0723 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 3) (by decide)
theorem parentRow_mem0724 : ParentOwnership.parentRow0724 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 4) (by decide)
theorem parentRow_mem0725 : ParentOwnership.parentRow0725 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 5) (by decide)
theorem parentRow_mem0726 : ParentOwnership.parentRow0726 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 6) (by decide)
theorem parentRow_mem0727 : ParentOwnership.parentRow0727 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 7) (by decide)
theorem parentRow_mem0728 : ParentOwnership.parentRow0728 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 8) (by decide)
theorem parentRow_mem0729 : ParentOwnership.parentRow0729 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 9) (by decide)
theorem parentRow_mem0730 : ParentOwnership.parentRow0730 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 10) (by decide)
theorem parentRow_mem0731 : ParentOwnership.parentRow0731 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 11) (by decide)
theorem parentRow_mem0732 : ParentOwnership.parentRow0732 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 12) (by decide)
theorem parentRow_mem0733 : ParentOwnership.parentRow0733 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 13) (by decide)
theorem parentRow_mem0734 : ParentOwnership.parentRow0734 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 14) (by decide)
theorem parentRow_mem0735 : ParentOwnership.parentRow0735 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows045, parentChunk_mem045, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows045) (n := 15) (by decide)
theorem parentChunk_mem046 : ParentOwnership.parentRows046 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 46) (by decide)
theorem parentRow_mem0736 : ParentOwnership.parentRow0736 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 0) (by decide)
theorem parentRow_mem0737 : ParentOwnership.parentRow0737 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 1) (by decide)
theorem parentRow_mem0738 : ParentOwnership.parentRow0738 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 2) (by decide)
theorem parentRow_mem0739 : ParentOwnership.parentRow0739 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 3) (by decide)
theorem parentRow_mem0740 : ParentOwnership.parentRow0740 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 4) (by decide)
theorem parentRow_mem0741 : ParentOwnership.parentRow0741 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 5) (by decide)
theorem parentRow_mem0742 : ParentOwnership.parentRow0742 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 6) (by decide)
theorem parentRow_mem0743 : ParentOwnership.parentRow0743 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 7) (by decide)
theorem parentRow_mem0744 : ParentOwnership.parentRow0744 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 8) (by decide)
theorem parentRow_mem0745 : ParentOwnership.parentRow0745 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 9) (by decide)
theorem parentRow_mem0746 : ParentOwnership.parentRow0746 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 10) (by decide)
theorem parentRow_mem0747 : ParentOwnership.parentRow0747 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 11) (by decide)
theorem parentRow_mem0748 : ParentOwnership.parentRow0748 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 12) (by decide)
theorem parentRow_mem0749 : ParentOwnership.parentRow0749 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 13) (by decide)
theorem parentRow_mem0750 : ParentOwnership.parentRow0750 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 14) (by decide)
theorem parentRow_mem0751 : ParentOwnership.parentRow0751 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows046, parentChunk_mem046, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows046) (n := 15) (by decide)
theorem parentChunk_mem047 : ParentOwnership.parentRows047 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 47) (by decide)
theorem parentRow_mem0752 : ParentOwnership.parentRow0752 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 0) (by decide)
theorem parentRow_mem0753 : ParentOwnership.parentRow0753 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 1) (by decide)
theorem parentRow_mem0754 : ParentOwnership.parentRow0754 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 2) (by decide)
theorem parentRow_mem0755 : ParentOwnership.parentRow0755 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 3) (by decide)
theorem parentRow_mem0756 : ParentOwnership.parentRow0756 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 4) (by decide)
theorem parentRow_mem0757 : ParentOwnership.parentRow0757 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 5) (by decide)
theorem parentRow_mem0758 : ParentOwnership.parentRow0758 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 6) (by decide)
theorem parentRow_mem0759 : ParentOwnership.parentRow0759 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 7) (by decide)
theorem parentRow_mem0760 : ParentOwnership.parentRow0760 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 8) (by decide)
theorem parentRow_mem0761 : ParentOwnership.parentRow0761 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 9) (by decide)
theorem parentRow_mem0762 : ParentOwnership.parentRow0762 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 10) (by decide)
theorem parentRow_mem0763 : ParentOwnership.parentRow0763 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 11) (by decide)
theorem parentRow_mem0764 : ParentOwnership.parentRow0764 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 12) (by decide)
theorem parentRow_mem0765 : ParentOwnership.parentRow0765 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 13) (by decide)
theorem parentRow_mem0766 : ParentOwnership.parentRow0766 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 14) (by decide)
theorem parentRow_mem0767 : ParentOwnership.parentRow0767 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows047, parentChunk_mem047, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows047) (n := 15) (by decide)

end SpectreFinite.HexSearch.RadiusFiveParentBinding
