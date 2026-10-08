module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose672 : Pose 7 := ⟨perm87, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row672_fields : pairFieldsMatchB 188160 facet0 facet587 key0 key672 rowPose672 = true := by decide +kernel
theorem row672_generated : rootPair 672 = some rowPose672 :=
  pairFieldsMatchB_sound (by decide) row672_fields
theorem row672_source : sourceKey 672 ∈ geometry.profile (sourceOwner 672) := by decide +kernel
theorem row672_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 580 key8).FastValid geometry rowPose672 := by decide +kernel
theorem row672_illegal : ¬ geometry.LegalContact rowPose672 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row672_reject_checked)
theorem row672_classified : RowClassified 672 := by
  intro p generated legal
  have he : rowPose672 = p := Option.some.inj (row672_generated.symm.trans generated)
  subst p
  exact (row672_illegal legal).elim

def rowPose673 : Pose 7 := ⟨perm111, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row673_fields : pairFieldsMatchB 188160 facet0 facet588 key0 key673 rowPose673 = true := by decide +kernel
theorem row673_generated : rootPair 673 = some rowPose673 :=
  pairFieldsMatchB_sound (by decide) row673_fields
theorem row673_source : sourceKey 673 ∈ geometry.profile (sourceOwner 673) := by decide +kernel
theorem row673_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 588 key1).FastValid geometry rowPose673 := by decide +kernel
theorem row673_illegal : ¬ geometry.LegalContact rowPose673 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row673_reject_checked)
theorem row673_classified : RowClassified 673 := by
  intro p generated legal
  have he : rowPose673 = p := Option.some.inj (row673_generated.symm.trans generated)
  subst p
  exact (row673_illegal legal).elim

def rowPose674 : Pose 7 := ⟨perm15, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row674_fields : pairFieldsMatchB 188160 facet0 facet589 key0 key674 rowPose674 = true := by decide +kernel
theorem row674_generated : rootPair 674 = some rowPose674 :=
  pairFieldsMatchB_sound (by decide) row674_fields
theorem row674_source : sourceKey 674 ∈ geometry.profile (sourceOwner 674) := by decide +kernel
theorem row674_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 589 key1).FastValid geometry rowPose674 := by decide +kernel
theorem row674_illegal : ¬ geometry.LegalContact rowPose674 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row674_reject_checked)
theorem row674_classified : RowClassified 674 := by
  intro p generated legal
  have he : rowPose674 = p := Option.some.inj (row674_generated.symm.trans generated)
  subst p
  exact (row674_illegal legal).elim

def rowPose675 : Pose 7 := ⟨perm24, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row675_fields : pairFieldsMatchB 188160 facet0 facet590 key0 key675 rowPose675 = true := by decide +kernel
theorem row675_generated : rootPair 675 = some rowPose675 :=
  pairFieldsMatchB_sound (by decide) row675_fields
theorem row675_source : sourceKey 675 ∈ geometry.profile (sourceOwner 675) := by decide +kernel
theorem row675_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 590 key1).FastValid geometry rowPose675 := by decide +kernel
theorem row675_illegal : ¬ geometry.LegalContact rowPose675 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row675_reject_checked)
theorem row675_classified : RowClassified 675 := by
  intro p generated legal
  have he : rowPose675 = p := Option.some.inj (row675_generated.symm.trans generated)
  subst p
  exact (row675_illegal legal).elim

def rowPose676 : Pose 7 := ⟨perm37, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row676_fields : pairFieldsMatchB 188160 facet0 facet591 key0 key676 rowPose676 = true := by decide +kernel
theorem row676_generated : rootPair 676 = some rowPose676 :=
  pairFieldsMatchB_sound (by decide) row676_fields
theorem row676_source : sourceKey 676 ∈ geometry.profile (sourceOwner 676) := by decide +kernel
theorem row676_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 591 key0).FastValid geometry rowPose676 := by decide +kernel
theorem row676_illegal : ¬ geometry.LegalContact rowPose676 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row676_reject_checked)
theorem row676_classified : RowClassified 676 := by
  intro p generated legal
  have he : rowPose676 = p := Option.some.inj (row676_generated.symm.trans generated)
  subst p
  exact (row676_illegal legal).elim

def rowPose677 : Pose 7 := ⟨perm42, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row677_fields : pairFieldsMatchB 188160 facet0 facet591 key0 key677 rowPose677 = true := by decide +kernel
theorem row677_generated : rootPair 677 = some rowPose677 :=
  pairFieldsMatchB_sound (by decide) row677_fields
theorem row677_source : sourceKey 677 ∈ geometry.profile (sourceOwner 677) := by decide +kernel
theorem row677_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 817 key8).FastValid geometry rowPose677 := by decide +kernel
theorem row677_illegal : ¬ geometry.LegalContact rowPose677 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row677_reject_checked)
theorem row677_classified : RowClassified 677 := by
  intro p generated legal
  have he : rowPose677 = p := Option.some.inj (row677_generated.symm.trans generated)
  subst p
  exact (row677_illegal legal).elim

def rowPose678 : Pose 7 := ⟨perm53, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row678_fields : pairFieldsMatchB 188160 facet0 facet592 key0 key678 rowPose678 = true := by decide +kernel
theorem row678_generated : rootPair 678 = some rowPose678 :=
  pairFieldsMatchB_sound (by decide) row678_fields
theorem row678_source : sourceKey 678 ∈ geometry.profile (sourceOwner 678) := by decide +kernel
theorem row678_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 592 key0).FastValid geometry rowPose678 := by decide +kernel
theorem row678_illegal : ¬ geometry.LegalContact rowPose678 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row678_reject_checked)
theorem row678_classified : RowClassified 678 := by
  intro p generated legal
  have he : rowPose678 = p := Option.some.inj (row678_generated.symm.trans generated)
  subst p
  exact (row678_illegal legal).elim

def rowPose679 : Pose 7 := ⟨perm74, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row679_fields : pairFieldsMatchB 188160 facet0 facet593 key0 key679 rowPose679 = true := by decide +kernel
theorem row679_generated : rootPair 679 = some rowPose679 :=
  pairFieldsMatchB_sound (by decide) row679_fields
theorem row679_source : sourceKey 679 ∈ geometry.profile (sourceOwner 679) := by decide +kernel
theorem row679_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 593 key0).FastValid geometry rowPose679 := by decide +kernel
theorem row679_illegal : ¬ geometry.LegalContact rowPose679 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row679_reject_checked)
theorem row679_classified : RowClassified 679 := by
  intro p generated legal
  have he : rowPose679 = p := Option.some.inj (row679_generated.symm.trans generated)
  subst p
  exact (row679_illegal legal).elim

def rowPose680 : Pose 7 := ⟨perm89, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row680_fields : pairFieldsMatchB 188160 facet0 facet594 key0 key680 rowPose680 = true := by decide +kernel
theorem row680_generated : rootPair 680 = some rowPose680 :=
  pairFieldsMatchB_sound (by decide) row680_fields
theorem row680_source : sourceKey 680 ∈ geometry.profile (sourceOwner 680) := by decide +kernel
theorem row680_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 594 key1).FastValid geometry rowPose680 := by decide +kernel
theorem row680_illegal : ¬ geometry.LegalContact rowPose680 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row680_reject_checked)
theorem row680_classified : RowClassified 680 := by
  intro p generated legal
  have he : rowPose680 = p := Option.some.inj (row680_generated.symm.trans generated)
  subst p
  exact (row680_illegal legal).elim

def rowPose681 : Pose 7 := ⟨perm101, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row681_fields : pairFieldsMatchB 188160 facet0 facet595 key0 key681 rowPose681 = true := by decide +kernel
theorem row681_generated : rootPair 681 = some rowPose681 :=
  pairFieldsMatchB_sound (by decide) row681_fields
theorem row681_source : sourceKey 681 ∈ geometry.profile (sourceOwner 681) := by decide +kernel
theorem row681_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 595 key0).FastValid geometry rowPose681 := by decide +kernel
theorem row681_illegal : ¬ geometry.LegalContact rowPose681 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row681_reject_checked)
theorem row681_classified : RowClassified 681 := by
  intro p generated legal
  have he : rowPose681 = p := Option.some.inj (row681_generated.symm.trans generated)
  subst p
  exact (row681_illegal legal).elim

def rowPose682 : Pose 7 := ⟨perm5, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row682_fields : pairFieldsMatchB 188160 facet0 facet596 key0 key682 rowPose682 = true := by decide +kernel
theorem row682_generated : rootPair 682 = some rowPose682 :=
  pairFieldsMatchB_sound (by decide) row682_fields
theorem row682_source : sourceKey 682 ∈ geometry.profile (sourceOwner 682) := by decide +kernel
theorem row682_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 596 key1).FastValid geometry rowPose682 := by decide +kernel
theorem row682_illegal : ¬ geometry.LegalContact rowPose682 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row682_reject_checked)
theorem row682_classified : RowClassified 682 := by
  intro p generated legal
  have he : rowPose682 = p := Option.some.inj (row682_generated.symm.trans generated)
  subst p
  exact (row682_illegal legal).elim

def rowPose683 : Pose 7 := ⟨perm21, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row683_fields : pairFieldsMatchB 188160 facet0 facet597 key0 key683 rowPose683 = true := by decide +kernel
theorem row683_generated : rootPair 683 = some rowPose683 :=
  pairFieldsMatchB_sound (by decide) row683_fields
theorem row683_source : sourceKey 683 ∈ geometry.profile (sourceOwner 683) := by decide +kernel
theorem row683_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 597 key0).FastValid geometry rowPose683 := by decide +kernel
theorem row683_illegal : ¬ geometry.LegalContact rowPose683 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row683_reject_checked)
theorem row683_classified : RowClassified 683 := by
  intro p generated legal
  have he : rowPose683 = p := Option.some.inj (row683_generated.symm.trans generated)
  subst p
  exact (row683_illegal legal).elim

def rowPose684 : Pose 7 := ⟨perm42, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row684_fields : pairFieldsMatchB 188160 facet0 facet598 key0 key684 rowPose684 = true := by decide +kernel
theorem row684_generated : rootPair 684 = some rowPose684 :=
  pairFieldsMatchB_sound (by decide) row684_fields
theorem row684_source : sourceKey 684 ∈ geometry.profile (sourceOwner 684) := by decide +kernel
theorem row684_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 598 key0).FastValid geometry rowPose684 := by decide +kernel
theorem row684_illegal : ¬ geometry.LegalContact rowPose684 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row684_reject_checked)
theorem row684_classified : RowClassified 684 := by
  intro p generated legal
  have he : rowPose684 = p := Option.some.inj (row684_generated.symm.trans generated)
  subst p
  exact (row684_illegal legal).elim

def rowPose685 : Pose 7 := ⟨perm53, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row685_fields : pairFieldsMatchB 188160 facet0 facet599 key0 key685 rowPose685 = true := by decide +kernel
theorem row685_generated : rootPair 685 = some rowPose685 :=
  pairFieldsMatchB_sound (by decide) row685_fields
theorem row685_source : sourceKey 685 ∈ geometry.profile (sourceOwner 685) := by decide +kernel
theorem row685_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 571 key8).FastValid geometry rowPose685 := by decide +kernel
theorem row685_illegal : ¬ geometry.LegalContact rowPose685 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row685_reject_checked)
theorem row685_classified : RowClassified 685 := by
  intro p generated legal
  have he : rowPose685 = p := Option.some.inj (row685_generated.symm.trans generated)
  subst p
  exact (row685_illegal legal).elim

def rowPose686 : Pose 7 := ⟨perm58, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row686_fields : pairFieldsMatchB 188160 facet0 facet599 key0 key686 rowPose686 = true := by decide +kernel
theorem row686_generated : rootPair 686 = some rowPose686 :=
  pairFieldsMatchB_sound (by decide) row686_fields
theorem row686_source : sourceKey 686 ∈ geometry.profile (sourceOwner 686) := by decide +kernel
theorem row686_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 599 key0).FastValid geometry rowPose686 := by decide +kernel
theorem row686_illegal : ¬ geometry.LegalContact rowPose686 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row686_reject_checked)
theorem row686_classified : RowClassified 686 := by
  intro p generated legal
  have he : rowPose686 = p := Option.some.inj (row686_generated.symm.trans generated)
  subst p
  exact (row686_illegal legal).elim

def rowPose687 : Pose 7 := ⟨perm69, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row687_fields : pairFieldsMatchB 188160 facet0 facet600 key0 key687 rowPose687 = true := by decide +kernel
theorem row687_generated : rootPair 687 = some rowPose687 :=
  pairFieldsMatchB_sound (by decide) row687_fields
theorem row687_source : sourceKey 687 ∈ geometry.profile (sourceOwner 687) := by decide +kernel
theorem row687_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 600 key1).FastValid geometry rowPose687 := by decide +kernel
theorem row687_illegal : ¬ geometry.LegalContact rowPose687 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row687_reject_checked)
theorem row687_classified : RowClassified 687 := by
  intro p generated legal
  have he : rowPose687 = p := Option.some.inj (row687_generated.symm.trans generated)
  subst p
  exact (row687_illegal legal).elim

def rowPose688 : Pose 7 := ⟨perm90, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row688_fields : pairFieldsMatchB 188160 facet0 facet601 key0 key688 rowPose688 = true := by decide +kernel
theorem row688_generated : rootPair 688 = some rowPose688 :=
  pairFieldsMatchB_sound (by decide) row688_fields
theorem row688_source : sourceKey 688 ∈ geometry.profile (sourceOwner 688) := by decide +kernel
theorem row688_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 601 key1).FastValid geometry rowPose688 := by decide +kernel
theorem row688_illegal : ¬ geometry.LegalContact rowPose688 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row688_reject_checked)
theorem row688_classified : RowClassified 688 := by
  intro p generated legal
  have he : rowPose688 = p := Option.some.inj (row688_generated.symm.trans generated)
  subst p
  exact (row688_illegal legal).elim

def rowPose689 : Pose 7 := ⟨perm106, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row689_fields : pairFieldsMatchB 188160 facet0 facet602 key0 key689 rowPose689 = true := by decide +kernel
theorem row689_generated : rootPair 689 = some rowPose689 :=
  pairFieldsMatchB_sound (by decide) row689_fields
theorem row689_source : sourceKey 689 ∈ geometry.profile (sourceOwner 689) := by decide +kernel
theorem row689_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 602 key0).FastValid geometry rowPose689 := by decide +kernel
theorem row689_illegal : ¬ geometry.LegalContact rowPose689 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row689_reject_checked)
theorem row689_classified : RowClassified 689 := by
  intro p generated legal
  have he : rowPose689 = p := Option.some.inj (row689_generated.symm.trans generated)
  subst p
  exact (row689_illegal legal).elim

def rowPose690 : Pose 7 := ⟨perm0, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row690_fields : pairFieldsMatchB 188160 facet0 facet603 key0 key690 rowPose690 = true := by decide +kernel
theorem row690_generated : rootPair 690 = some rowPose690 :=
  pairFieldsMatchB_sound (by decide) row690_fields
theorem row690_source : sourceKey 690 ∈ geometry.profile (sourceOwner 690) := by decide +kernel
theorem row690_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 603 key0).FastValid geometry rowPose690 := by decide +kernel
theorem row690_illegal : ¬ geometry.LegalContact rowPose690 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row690_reject_checked)
theorem row690_classified : RowClassified 690 := by
  intro p generated legal
  have he : rowPose690 = p := Option.some.inj (row690_generated.symm.trans generated)
  subst p
  exact (row690_illegal legal).elim

def rowPose691 : Pose 7 := ⟨perm21, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row691_fields : pairFieldsMatchB 188160 facet0 facet604 key0 key691 rowPose691 = true := by decide +kernel
theorem row691_generated : rootPair 691 = some rowPose691 :=
  pairFieldsMatchB_sound (by decide) row691_fields
theorem row691_source : sourceKey 691 ∈ geometry.profile (sourceOwner 691) := by decide +kernel
theorem row691_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 492 key8).FastValid geometry rowPose691 := by decide +kernel
theorem row691_illegal : ¬ geometry.LegalContact rowPose691 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row691_reject_checked)
theorem row691_classified : RowClassified 691 := by
  intro p generated legal
  have he : rowPose691 = p := Option.some.inj (row691_generated.symm.trans generated)
  subst p
  exact (row691_illegal legal).elim

def rowPose692 : Pose 7 := ⟨perm24, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row692_fields : pairFieldsMatchB 188160 facet0 facet604 key0 key692 rowPose692 = true := by decide +kernel
theorem row692_generated : rootPair 692 = some rowPose692 :=
  pairFieldsMatchB_sound (by decide) row692_fields
theorem row692_source : sourceKey 692 ∈ geometry.profile (sourceOwner 692) := by decide +kernel
theorem row692_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 604 key0).FastValid geometry rowPose692 := by decide +kernel
theorem row692_illegal : ¬ geometry.LegalContact rowPose692 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row692_reject_checked)
theorem row692_classified : RowClassified 692 := by
  intro p generated legal
  have he : rowPose692 = p := Option.some.inj (row692_generated.symm.trans generated)
  subst p
  exact (row692_illegal legal).elim

def rowPose693 : Pose 7 := ⟨perm37, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row693_fields : pairFieldsMatchB 188160 facet0 facet605 key0 key693 rowPose693 = true := by decide +kernel
theorem row693_generated : rootPair 693 = some rowPose693 :=
  pairFieldsMatchB_sound (by decide) row693_fields
theorem row693_source : sourceKey 693 ∈ geometry.profile (sourceOwner 693) := by decide +kernel
theorem row693_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 605 key1).FastValid geometry rowPose693 := by decide +kernel
theorem row693_illegal : ¬ geometry.LegalContact rowPose693 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row693_reject_checked)
theorem row693_classified : RowClassified 693 := by
  intro p generated legal
  have he : rowPose693 = p := Option.some.inj (row693_generated.symm.trans generated)
  subst p
  exact (row693_illegal legal).elim

def rowPose694 : Pose 7 := ⟨perm58, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row694_fields : pairFieldsMatchB 188160 facet0 facet606 key0 key694 rowPose694 = true := by decide +kernel
theorem row694_generated : rootPair 694 = some rowPose694 :=
  pairFieldsMatchB_sound (by decide) row694_fields
theorem row694_source : sourceKey 694 ∈ geometry.profile (sourceOwner 694) := by decide +kernel
theorem row694_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 606 key1).FastValid geometry rowPose694 := by decide +kernel
theorem row694_illegal : ¬ geometry.LegalContact rowPose694 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row694_reject_checked)
theorem row694_classified : RowClassified 694 := by
  intro p generated legal
  have he : rowPose694 = p := Option.some.inj (row694_generated.symm.trans generated)
  subst p
  exact (row694_illegal legal).elim

def rowPose695 : Pose 7 := ⟨perm71, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row695_fields : pairFieldsMatchB 188160 facet0 facet607 key0 key695 rowPose695 = true := by decide +kernel
theorem row695_generated : rootPair 695 = some rowPose695 :=
  pairFieldsMatchB_sound (by decide) row695_fields
theorem row695_source : sourceKey 695 ∈ geometry.profile (sourceOwner 695) := by decide +kernel
theorem row695_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 607 key0).FastValid geometry rowPose695 := by decide +kernel
theorem row695_illegal : ¬ geometry.LegalContact rowPose695 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row695_reject_checked)
theorem row695_classified : RowClassified 695 := by
  intro p generated legal
  have he : rowPose695 = p := Option.some.inj (row695_generated.symm.trans generated)
  subst p
  exact (row695_illegal legal).elim

def rowPose696 : Pose 7 := ⟨perm95, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row696_fields : pairFieldsMatchB 188160 facet0 facet608 key0 key696 rowPose696 = true := by decide +kernel
theorem row696_generated : rootPair 696 = some rowPose696 :=
  pairFieldsMatchB_sound (by decide) row696_fields
theorem row696_source : sourceKey 696 ∈ geometry.profile (sourceOwner 696) := by decide +kernel
theorem row696_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 608 key1).FastValid geometry rowPose696 := by decide +kernel
theorem row696_illegal : ¬ geometry.LegalContact rowPose696 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row696_reject_checked)
theorem row696_classified : RowClassified 696 := by
  intro p generated legal
  have he : rowPose696 = p := Option.some.inj (row696_generated.symm.trans generated)
  subst p
  exact (row696_illegal legal).elim

def rowPose697 : Pose 7 := ⟨perm111, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row697_fields : pairFieldsMatchB 188160 facet0 facet609 key0 key697 rowPose697 = true := by decide +kernel
theorem row697_generated : rootPair 697 = some rowPose697 :=
  pairFieldsMatchB_sound (by decide) row697_fields
theorem row697_source : sourceKey 697 ∈ geometry.profile (sourceOwner 697) := by decide +kernel
theorem row697_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 609 key0).FastValid geometry rowPose697 := by decide +kernel
theorem row697_illegal : ¬ geometry.LegalContact rowPose697 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row697_reject_checked)
theorem row697_classified : RowClassified 697 := by
  intro p generated legal
  have he : rowPose697 = p := Option.some.inj (row697_generated.symm.trans generated)
  subst p
  exact (row697_illegal legal).elim

def rowPose698 : Pose 7 := ⟨perm15, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row698_fields : pairFieldsMatchB 188160 facet0 facet610 key0 key698 rowPose698 = true := by decide +kernel
theorem row698_generated : rootPair 698 = some rowPose698 :=
  pairFieldsMatchB_sound (by decide) row698_fields
theorem row698_source : sourceKey 698 ∈ geometry.profile (sourceOwner 698) := by decide +kernel
theorem row698_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 610 key1).FastValid geometry rowPose698 := by decide +kernel
theorem row698_illegal : ¬ geometry.LegalContact rowPose698 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row698_reject_checked)
theorem row698_classified : RowClassified 698 := by
  intro p generated legal
  have he : rowPose698 = p := Option.some.inj (row698_generated.symm.trans generated)
  subst p
  exact (row698_illegal legal).elim

def rowPose699 : Pose 7 := ⟨perm24, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row699_fields : pairFieldsMatchB 188160 facet0 facet611 key0 key699 rowPose699 = true := by decide +kernel
theorem row699_generated : rootPair 699 = some rowPose699 :=
  pairFieldsMatchB_sound (by decide) row699_fields
theorem row699_source : sourceKey 699 ∈ geometry.profile (sourceOwner 699) := by decide +kernel
theorem row699_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 611 key1).FastValid geometry rowPose699 := by decide +kernel
theorem row699_illegal : ¬ geometry.LegalContact rowPose699 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row699_reject_checked)
theorem row699_classified : RowClassified 699 := by
  intro p generated legal
  have he : rowPose699 = p := Option.some.inj (row699_generated.symm.trans generated)
  subst p
  exact (row699_illegal legal).elim

def rowPose700 : Pose 7 := ⟨perm37, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row700_fields : pairFieldsMatchB 188160 facet0 facet612 key0 key700 rowPose700 = true := by decide +kernel
theorem row700_generated : rootPair 700 = some rowPose700 :=
  pairFieldsMatchB_sound (by decide) row700_fields
theorem row700_source : sourceKey 700 ∈ geometry.profile (sourceOwner 700) := by decide +kernel
theorem row700_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 612 key0).FastValid geometry rowPose700 := by decide +kernel
theorem row700_illegal : ¬ geometry.LegalContact rowPose700 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row700_reject_checked)
theorem row700_classified : RowClassified 700 := by
  intro p generated legal
  have he : rowPose700 = p := Option.some.inj (row700_generated.symm.trans generated)
  subst p
  exact (row700_illegal legal).elim

def rowPose701 : Pose 7 := ⟨perm42, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row701_fields : pairFieldsMatchB 188160 facet0 facet612 key0 key701 rowPose701 = true := by decide +kernel
theorem row701_generated : rootPair 701 = some rowPose701 :=
  pairFieldsMatchB_sound (by decide) row701_fields
theorem row701_source : sourceKey 701 ∈ geometry.profile (sourceOwner 701) := by decide +kernel
theorem row701_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 838 key8).FastValid geometry rowPose701 := by decide +kernel
theorem row701_illegal : ¬ geometry.LegalContact rowPose701 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row701_reject_checked)
theorem row701_classified : RowClassified 701 := by
  intro p generated legal
  have he : rowPose701 = p := Option.some.inj (row701_generated.symm.trans generated)
  subst p
  exact (row701_illegal legal).elim

def rowPose702 : Pose 7 := ⟨perm53, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row702_fields : pairFieldsMatchB 188160 facet0 facet613 key0 key702 rowPose702 = true := by decide +kernel
theorem row702_generated : rootPair 702 = some rowPose702 :=
  pairFieldsMatchB_sound (by decide) row702_fields
theorem row702_source : sourceKey 702 ∈ geometry.profile (sourceOwner 702) := by decide +kernel
theorem row702_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 613 key0).FastValid geometry rowPose702 := by decide +kernel
theorem row702_illegal : ¬ geometry.LegalContact rowPose702 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row702_reject_checked)
theorem row702_classified : RowClassified 702 := by
  intro p generated legal
  have he : rowPose702 = p := Option.some.inj (row702_generated.symm.trans generated)
  subst p
  exact (row702_illegal legal).elim

def rowPose703 : Pose 7 := ⟨perm74, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row703_fields : pairFieldsMatchB 188160 facet0 facet614 key0 key703 rowPose703 = true := by decide +kernel
theorem row703_generated : rootPair 703 = some rowPose703 :=
  pairFieldsMatchB_sound (by decide) row703_fields
theorem row703_source : sourceKey 703 ∈ geometry.profile (sourceOwner 703) := by decide +kernel
theorem row703_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 614 key0).FastValid geometry rowPose703 := by decide +kernel
theorem row703_illegal : ¬ geometry.LegalContact rowPose703 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row703_reject_checked)
theorem row703_classified : RowClassified 703 := by
  intro p generated legal
  have he : rowPose703 = p := Option.some.inj (row703_generated.symm.trans generated)
  subst p
  exact (row703_illegal legal).elim

theorem chunk21_classified (i : Fin 32) : RowClassified ⟨672 + i.val, by omega⟩ := by
  fin_cases i
  · exact row672_classified
  · exact row673_classified
  · exact row674_classified
  · exact row675_classified
  · exact row676_classified
  · exact row677_classified
  · exact row678_classified
  · exact row679_classified
  · exact row680_classified
  · exact row681_classified
  · exact row682_classified
  · exact row683_classified
  · exact row684_classified
  · exact row685_classified
  · exact row686_classified
  · exact row687_classified
  · exact row688_classified
  · exact row689_classified
  · exact row690_classified
  · exact row691_classified
  · exact row692_classified
  · exact row693_classified
  · exact row694_classified
  · exact row695_classified
  · exact row696_classified
  · exact row697_classified
  · exact row698_classified
  · exact row699_classified
  · exact row700_classified
  · exact row701_classified
  · exact row702_classified
  · exact row703_classified

theorem chunk21_source (i : Fin 32) : sourceKey ⟨672 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨672 + i.val, by omega⟩) := by
  fin_cases i
  · exact row672_source
  · exact row673_source
  · exact row674_source
  · exact row675_source
  · exact row676_source
  · exact row677_source
  · exact row678_source
  · exact row679_source
  · exact row680_source
  · exact row681_source
  · exact row682_source
  · exact row683_source
  · exact row684_source
  · exact row685_source
  · exact row686_source
  · exact row687_source
  · exact row688_source
  · exact row689_source
  · exact row690_source
  · exact row691_source
  · exact row692_source
  · exact row693_source
  · exact row694_source
  · exact row695_source
  · exact row696_source
  · exact row697_source
  · exact row698_source
  · exact row699_source
  · exact row700_source
  · exact row701_source
  · exact row702_source
  · exact row703_source

#print axioms chunk21_classified
end SparseMonotiles.Contact.RootZeroPilot7
