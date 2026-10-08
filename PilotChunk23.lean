module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose736 : Pose 7 := ⟨perm96, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row736_fields : pairFieldsMatchB 188160 facet0 facet644 key0 key736 rowPose736 = true := by decide +kernel
theorem row736_generated : rootPair 736 = some rowPose736 :=
  pairFieldsMatchB_sound (by decide) row736_fields
theorem row736_source : sourceKey 736 ∈ geometry.profile (sourceOwner 736) := by decide +kernel
theorem row736_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 630 key8).FastValid geometry rowPose736 := by decide +kernel
theorem row736_illegal : ¬ geometry.LegalContact rowPose736 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row736_reject_checked)
theorem row736_classified : RowClassified 736 := by
  intro p generated legal
  have he : rowPose736 = p := Option.some.inj (row736_generated.symm.trans generated)
  subst p
  exact (row736_illegal legal).elim

def rowPose737 : Pose 7 := ⟨perm111, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row737_fields : pairFieldsMatchB 188160 facet0 facet644 key0 key737 rowPose737 = true := by decide +kernel
theorem row737_generated : rootPair 737 = some rowPose737 :=
  pairFieldsMatchB_sound (by decide) row737_fields
theorem row737_source : sourceKey 737 ∈ geometry.profile (sourceOwner 737) := by decide +kernel
theorem row737_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 644 key0).FastValid geometry rowPose737 := by decide +kernel
theorem row737_illegal : ¬ geometry.LegalContact rowPose737 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row737_reject_checked)
theorem row737_classified : RowClassified 737 := by
  intro p generated legal
  have he : rowPose737 = p := Option.some.inj (row737_generated.symm.trans generated)
  subst p
  exact (row737_illegal legal).elim

def rowPose738 : Pose 7 := ⟨perm10, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row738_fields : pairFieldsMatchB 188160 facet0 facet645 key0 key738 rowPose738 = true := by decide +kernel
theorem row738_generated : rootPair 738 = some rowPose738 :=
  pairFieldsMatchB_sound (by decide) row738_fields
theorem row738_source : sourceKey 738 ∈ geometry.profile (sourceOwner 738) := by decide +kernel
theorem row738_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 645 key0).FastValid geometry rowPose738 := by decide +kernel
theorem row738_illegal : ¬ geometry.LegalContact rowPose738 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row738_reject_checked)
theorem row738_classified : RowClassified 738 := by
  intro p generated legal
  have he : rowPose738 = p := Option.some.inj (row738_generated.symm.trans generated)
  subst p
  exact (row738_illegal legal).elim

def rowPose739 : Pose 7 := ⟨perm22, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row739_fields : pairFieldsMatchB 188160 facet0 facet646 key0 key739 rowPose739 = true := by decide +kernel
theorem row739_generated : rootPair 739 = some rowPose739 :=
  pairFieldsMatchB_sound (by decide) row739_fields
theorem row739_source : sourceKey 739 ∈ geometry.profile (sourceOwner 739) := by decide +kernel
theorem row739_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 646 key1).FastValid geometry rowPose739 := by decide +kernel
theorem row739_illegal : ¬ geometry.LegalContact rowPose739 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row739_reject_checked)
theorem row739_classified : RowClassified 739 := by
  intro p generated legal
  have he : rowPose739 = p := Option.some.inj (row739_generated.symm.trans generated)
  subst p
  exact (row739_illegal legal).elim

def rowPose740 : Pose 7 := ⟨perm37, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row740_fields : pairFieldsMatchB 188160 facet0 facet647 key0 key740 rowPose740 = true := by decide +kernel
theorem row740_generated : rootPair 740 = some rowPose740 :=
  pairFieldsMatchB_sound (by decide) row740_fields
theorem row740_source : sourceKey 740 ∈ geometry.profile (sourceOwner 740) := by decide +kernel
theorem row740_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 647 key0).FastValid geometry rowPose740 := by decide +kernel
theorem row740_illegal : ¬ geometry.LegalContact rowPose740 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row740_reject_checked)
theorem row740_classified : RowClassified 740 := by
  intro p generated legal
  have he : rowPose740 = p := Option.some.inj (row740_generated.symm.trans generated)
  subst p
  exact (row740_illegal legal).elim

def rowPose741 : Pose 7 := ⟨perm58, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row741_fields : pairFieldsMatchB 188160 facet0 facet648 key0 key741 rowPose741 = true := by decide +kernel
theorem row741_generated : rootPair 741 = some rowPose741 :=
  pairFieldsMatchB_sound (by decide) row741_fields
theorem row741_source : sourceKey 741 ∈ geometry.profile (sourceOwner 741) := by decide +kernel
theorem row741_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 648 key0).FastValid geometry rowPose741 := by decide +kernel
theorem row741_illegal : ¬ geometry.LegalContact rowPose741 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row741_reject_checked)
theorem row741_classified : RowClassified 741 := by
  intro p generated legal
  have he : rowPose741 = p := Option.some.inj (row741_generated.symm.trans generated)
  subst p
  exact (row741_illegal legal).elim

def rowPose742 : Pose 7 := ⟨perm74, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row742_fields : pairFieldsMatchB 188160 facet0 facet649 key0 key742 rowPose742 = true := by decide +kernel
theorem row742_generated : rootPair 742 = some rowPose742 :=
  pairFieldsMatchB_sound (by decide) row742_fields
theorem row742_source : sourceKey 742 ∈ geometry.profile (sourceOwner 742) := by decide +kernel
theorem row742_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 649 key0).FastValid geometry rowPose742 := by decide +kernel
theorem row742_illegal : ¬ geometry.LegalContact rowPose742 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row742_reject_checked)
theorem row742_classified : RowClassified 742 := by
  intro p generated legal
  have he : rowPose742 = p := Option.some.inj (row742_generated.symm.trans generated)
  subst p
  exact (row742_illegal legal).elim

def rowPose743 : Pose 7 := ⟨perm69, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row743_fields : pairFieldsMatchB 188160 facet0 facet649 key0 key743 rowPose743 = true := by decide +kernel
theorem row743_generated : rootPair 743 = some rowPose743 :=
  pairFieldsMatchB_sound (by decide) row743_fields
theorem row743_source : sourceKey 743 ∈ geometry.profile (sourceOwner 743) := by decide +kernel
theorem row743_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 663 key8).FastValid geometry rowPose743 := by decide +kernel
theorem row743_illegal : ¬ geometry.LegalContact rowPose743 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row743_reject_checked)
theorem row743_classified : RowClassified 743 := by
  intro p generated legal
  have he : rowPose743 = p := Option.some.inj (row743_generated.symm.trans generated)
  subst p
  exact (row743_illegal legal).elim

def rowPose744 : Pose 7 := ⟨perm87, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row744_fields : pairFieldsMatchB 188160 facet0 facet650 key0 key744 rowPose744 = true := by decide +kernel
theorem row744_generated : rootPair 744 = some rowPose744 :=
  pairFieldsMatchB_sound (by decide) row744_fields
theorem row744_source : sourceKey 744 ∈ geometry.profile (sourceOwner 744) := by decide +kernel
theorem row744_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 650 key1).FastValid geometry rowPose744 := by decide +kernel
theorem row744_illegal : ¬ geometry.LegalContact rowPose744 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row744_reject_checked)
theorem row744_classified : RowClassified 744 := by
  intro p generated legal
  have he : rowPose744 = p := Option.some.inj (row744_generated.symm.trans generated)
  subst p
  exact (row744_illegal legal).elim

def rowPose745 : Pose 7 := ⟨perm96, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row745_fields : pairFieldsMatchB 188160 facet0 facet651 key0 key745 rowPose745 = true := by decide +kernel
theorem row745_generated : rootPair 745 = some rowPose745 :=
  pairFieldsMatchB_sound (by decide) row745_fields
theorem row745_source : sourceKey 745 ∈ geometry.profile (sourceOwner 745) := by decide +kernel
theorem row745_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 651 key1).FastValid geometry rowPose745 := by decide +kernel
theorem row745_illegal : ¬ geometry.LegalContact rowPose745 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row745_reject_checked)
theorem row745_classified : RowClassified 745 := by
  intro p generated legal
  have he : rowPose745 = p := Option.some.inj (row745_generated.symm.trans generated)
  subst p
  exact (row745_illegal legal).elim

def rowPose746 : Pose 7 := ⟨perm5, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row746_fields : pairFieldsMatchB 188160 facet0 facet652 key0 key746 rowPose746 = true := by decide +kernel
theorem row746_generated : rootPair 746 = some rowPose746 :=
  pairFieldsMatchB_sound (by decide) row746_fields
theorem row746_source : sourceKey 746 ∈ geometry.profile (sourceOwner 746) := by decide +kernel
theorem row746_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 652 key0).FastValid geometry rowPose746 := by decide +kernel
theorem row746_illegal : ¬ geometry.LegalContact rowPose746 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row746_reject_checked)
theorem row746_classified : RowClassified 746 := by
  intro p generated legal
  have he : rowPose746 = p := Option.some.inj (row746_generated.symm.trans generated)
  subst p
  exact (row746_illegal legal).elim

def rowPose747 : Pose 7 := ⟨perm21, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row747_fields : pairFieldsMatchB 188160 facet0 facet653 key0 key747 rowPose747 = true := by decide +kernel
theorem row747_generated : rootPair 747 = some rowPose747 :=
  pairFieldsMatchB_sound (by decide) row747_fields
theorem row747_source : sourceKey 747 ∈ geometry.profile (sourceOwner 747) := by decide +kernel
theorem row747_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 653 key1).FastValid geometry rowPose747 := by decide +kernel
theorem row747_illegal : ¬ geometry.LegalContact rowPose747 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row747_reject_checked)
theorem row747_classified : RowClassified 747 := by
  intro p generated legal
  have he : rowPose747 = p := Option.some.inj (row747_generated.symm.trans generated)
  subst p
  exact (row747_illegal legal).elim

def rowPose748 : Pose 7 := ⟨perm42, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row748_fields : pairFieldsMatchB 188160 facet0 facet654 key0 key748 rowPose748 = true := by decide +kernel
theorem row748_generated : rootPair 748 = some rowPose748 :=
  pairFieldsMatchB_sound (by decide) row748_fields
theorem row748_source : sourceKey 748 ∈ geometry.profile (sourceOwner 748) := by decide +kernel
theorem row748_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 654 key1).FastValid geometry rowPose748 := by decide +kernel
theorem row748_illegal : ¬ geometry.LegalContact rowPose748 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row748_reject_checked)
theorem row748_classified : RowClassified 748 := by
  intro p generated legal
  have he : rowPose748 = p := Option.some.inj (row748_generated.symm.trans generated)
  subst p
  exact (row748_illegal legal).elim

def rowPose749 : Pose 7 := ⟨perm53, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row749_fields : pairFieldsMatchB 188160 facet0 facet655 key0 key749 rowPose749 = true := by decide +kernel
theorem row749_generated : rootPair 749 = some rowPose749 :=
  pairFieldsMatchB_sound (by decide) row749_fields
theorem row749_source : sourceKey 749 ∈ geometry.profile (sourceOwner 749) := by decide +kernel
theorem row749_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 655 key0).FastValid geometry rowPose749 := by decide +kernel
theorem row749_illegal : ¬ geometry.LegalContact rowPose749 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row749_reject_checked)
theorem row749_classified : RowClassified 749 := by
  intro p generated legal
  have he : rowPose749 = p := Option.some.inj (row749_generated.symm.trans generated)
  subst p
  exact (row749_illegal legal).elim

def rowPose750 : Pose 7 := ⟨perm58, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row750_fields : pairFieldsMatchB 188160 facet0 facet655 key0 key750 rowPose750 = true := by decide +kernel
theorem row750_generated : rootPair 750 = some rowPose750 :=
  pairFieldsMatchB_sound (by decide) row750_fields
theorem row750_source : sourceKey 750 ∈ geometry.profile (sourceOwner 750) := by decide +kernel
theorem row750_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 543 key8).FastValid geometry rowPose750 := by decide +kernel
theorem row750_illegal : ¬ geometry.LegalContact rowPose750 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row750_reject_checked)
theorem row750_classified : RowClassified 750 := by
  intro p generated legal
  have he : rowPose750 = p := Option.some.inj (row750_generated.symm.trans generated)
  subst p
  exact (row750_illegal legal).elim

def rowPose751 : Pose 7 := ⟨perm69, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row751_fields : pairFieldsMatchB 188160 facet0 facet656 key0 key751 rowPose751 = true := by decide +kernel
theorem row751_generated : rootPair 751 = some rowPose751 :=
  pairFieldsMatchB_sound (by decide) row751_fields
theorem row751_source : sourceKey 751 ∈ geometry.profile (sourceOwner 751) := by decide +kernel
theorem row751_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 656 key0).FastValid geometry rowPose751 := by decide +kernel
theorem row751_illegal : ¬ geometry.LegalContact rowPose751 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row751_reject_checked)
theorem row751_classified : RowClassified 751 := by
  intro p generated legal
  have he : rowPose751 = p := Option.some.inj (row751_generated.symm.trans generated)
  subst p
  exact (row751_illegal legal).elim

def rowPose752 : Pose 7 := ⟨perm90, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row752_fields : pairFieldsMatchB 188160 facet0 facet657 key0 key752 rowPose752 = true := by decide +kernel
theorem row752_generated : rootPair 752 = some rowPose752 :=
  pairFieldsMatchB_sound (by decide) row752_fields
theorem row752_source : sourceKey 752 ∈ geometry.profile (sourceOwner 752) := by decide +kernel
theorem row752_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 657 key0).FastValid geometry rowPose752 := by decide +kernel
theorem row752_illegal : ¬ geometry.LegalContact rowPose752 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row752_reject_checked)
theorem row752_classified : RowClassified 752 := by
  intro p generated legal
  have he : rowPose752 = p := Option.some.inj (row752_generated.symm.trans generated)
  subst p
  exact (row752_illegal legal).elim

def rowPose753 : Pose 7 := ⟨perm106, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row753_fields : pairFieldsMatchB 188160 facet0 facet658 key0 key753 rowPose753 = true := by decide +kernel
theorem row753_generated : rootPair 753 = some rowPose753 :=
  pairFieldsMatchB_sound (by decide) row753_fields
theorem row753_source : sourceKey 753 ∈ geometry.profile (sourceOwner 753) := by decide +kernel
theorem row753_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 658 key1).FastValid geometry rowPose753 := by decide +kernel
theorem row753_illegal : ¬ geometry.LegalContact rowPose753 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row753_reject_checked)
theorem row753_classified : RowClassified 753 := by
  intro p generated legal
  have he : rowPose753 = p := Option.some.inj (row753_generated.symm.trans generated)
  subst p
  exact (row753_illegal legal).elim

def rowPose754 : Pose 7 := ⟨perm0, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row754_fields : pairFieldsMatchB 188160 facet0 facet659 key0 key754 rowPose754 = true := by decide +kernel
theorem row754_generated : rootPair 754 = some rowPose754 :=
  pairFieldsMatchB_sound (by decide) row754_fields
theorem row754_source : sourceKey 754 ∈ geometry.profile (sourceOwner 754) := by decide +kernel
theorem row754_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 666 key8).FastValid geometry rowPose754 := by decide +kernel
theorem row754_illegal : ¬ geometry.LegalContact rowPose754 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row754_reject_checked)
theorem row754_classified : RowClassified 754 := by
  intro p generated legal
  have he : rowPose754 = p := Option.some.inj (row754_generated.symm.trans generated)
  subst p
  exact (row754_illegal legal).elim

def rowPose755 : Pose 7 := ⟨perm15, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row755_fields : pairFieldsMatchB 188160 facet0 facet659 key0 key755 rowPose755 = true := by decide +kernel
theorem row755_generated : rootPair 755 = some rowPose755 :=
  pairFieldsMatchB_sound (by decide) row755_fields
theorem row755_source : sourceKey 755 ∈ geometry.profile (sourceOwner 755) := by decide +kernel
theorem row755_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 659 key0).FastValid geometry rowPose755 := by decide +kernel
theorem row755_illegal : ¬ geometry.LegalContact rowPose755 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row755_reject_checked)
theorem row755_classified : RowClassified 755 := by
  intro p generated legal
  have he : rowPose755 = p := Option.some.inj (row755_generated.symm.trans generated)
  subst p
  exact (row755_illegal legal).elim

def rowPose756 : Pose 7 := ⟨perm21, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row756_fields : pairFieldsMatchB 188160 facet0 facet660 key0 key756 rowPose756 = true := by decide +kernel
theorem row756_generated : rootPair 756 = some rowPose756 :=
  pairFieldsMatchB_sound (by decide) row756_fields
theorem row756_source : sourceKey 756 ∈ geometry.profile (sourceOwner 756) := by decide +kernel
theorem row756_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 660 key0).FastValid geometry rowPose756 := by decide +kernel
theorem row756_illegal : ¬ geometry.LegalContact rowPose756 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row756_reject_checked)
theorem row756_classified : RowClassified 756 := by
  intro p generated legal
  have he : rowPose756 = p := Option.some.inj (row756_generated.symm.trans generated)
  subst p
  exact (row756_illegal legal).elim

def rowPose757 : Pose 7 := ⟨perm42, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row757_fields : pairFieldsMatchB 188160 facet0 facet661 key0 key757 rowPose757 = true := by decide +kernel
theorem row757_generated : rootPair 757 = some rowPose757 :=
  pairFieldsMatchB_sound (by decide) row757_fields
theorem row757_source : sourceKey 757 ∈ geometry.profile (sourceOwner 757) := by decide +kernel
theorem row757_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 661 key0).FastValid geometry rowPose757 := by decide +kernel
theorem row757_illegal : ¬ geometry.LegalContact rowPose757 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row757_reject_checked)
theorem row757_classified : RowClassified 757 := by
  intro p generated legal
  have he : rowPose757 = p := Option.some.inj (row757_generated.symm.trans generated)
  subst p
  exact (row757_illegal legal).elim

def rowPose758 : Pose 7 := ⟨perm55, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row758_fields : pairFieldsMatchB 188160 facet0 facet662 key0 key758 rowPose758 = true := by decide +kernel
theorem row758_generated : rootPair 758 = some rowPose758 :=
  pairFieldsMatchB_sound (by decide) row758_fields
theorem row758_source : sourceKey 758 ∈ geometry.profile (sourceOwner 758) := by decide +kernel
theorem row758_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 662 key1).FastValid geometry rowPose758 := by decide +kernel
theorem row758_illegal : ¬ geometry.LegalContact rowPose758 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row758_reject_checked)
theorem row758_classified : RowClassified 758 := by
  intro p generated legal
  have he : rowPose758 = p := Option.some.inj (row758_generated.symm.trans generated)
  subst p
  exact (row758_illegal legal).elim

def rowPose759 : Pose 7 := ⟨perm73, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row759_fields : pairFieldsMatchB 188160 facet0 facet663 key0 key759 rowPose759 = true := by decide +kernel
theorem row759_generated : rootPair 759 = some rowPose759 :=
  pairFieldsMatchB_sound (by decide) row759_fields
theorem row759_source : sourceKey 759 ∈ geometry.profile (sourceOwner 759) := by decide +kernel
theorem row759_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 663 key0).FastValid geometry rowPose759 := by decide +kernel
theorem row759_illegal : ¬ geometry.LegalContact rowPose759 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row759_reject_checked)
theorem row759_classified : RowClassified 759 := by
  intro p generated legal
  have he : rowPose759 = p := Option.some.inj (row759_generated.symm.trans generated)
  subst p
  exact (row759_illegal legal).elim

def rowPose760 : Pose 7 := ⟨perm87, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row760_fields : pairFieldsMatchB 188160 facet0 facet664 key0 key760 rowPose760 = true := by decide +kernel
theorem row760_generated : rootPair 760 = some rowPose760 :=
  pairFieldsMatchB_sound (by decide) row760_fields
theorem row760_source : sourceKey 760 ∈ geometry.profile (sourceOwner 760) := by decide +kernel
theorem row760_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 664 key1).FastValid geometry rowPose760 := by decide +kernel
theorem row760_illegal : ¬ geometry.LegalContact rowPose760 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row760_reject_checked)
theorem row760_classified : RowClassified 760 := by
  intro p generated legal
  have he : rowPose760 = p := Option.some.inj (row760_generated.symm.trans generated)
  subst p
  exact (row760_illegal legal).elim

def rowPose761 : Pose 7 := ⟨perm96, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row761_fields : pairFieldsMatchB 188160 facet0 facet665 key0 key761 rowPose761 = true := by decide +kernel
theorem row761_generated : rootPair 761 = some rowPose761 :=
  pairFieldsMatchB_sound (by decide) row761_fields
theorem row761_source : sourceKey 761 ∈ geometry.profile (sourceOwner 761) := by decide +kernel
theorem row761_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 665 key1).FastValid geometry rowPose761 := by decide +kernel
theorem row761_illegal : ¬ geometry.LegalContact rowPose761 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row761_reject_checked)
theorem row761_classified : RowClassified 761 := by
  intro p generated legal
  have he : rowPose761 = p := Option.some.inj (row761_generated.symm.trans generated)
  subst p
  exact (row761_illegal legal).elim

def rowPose762 : Pose 7 := ⟨perm0, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row762_fields : pairFieldsMatchB 188160 facet0 facet666 key0 key762 rowPose762 = true := by decide +kernel
theorem row762_generated : rootPair 762 = some rowPose762 :=
  pairFieldsMatchB_sound (by decide) row762_fields
theorem row762_source : sourceKey 762 ∈ geometry.profile (sourceOwner 762) := by decide +kernel
theorem row762_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 666 key0).FastValid geometry rowPose762 := by decide +kernel
theorem row762_illegal : ¬ geometry.LegalContact rowPose762 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row762_reject_checked)
theorem row762_classified : RowClassified 762 := by
  intro p generated legal
  have he : rowPose762 = p := Option.some.inj (row762_generated.symm.trans generated)
  subst p
  exact (row762_illegal legal).elim

def rowPose763 : Pose 7 := ⟨perm21, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row763_fields : pairFieldsMatchB 188160 facet0 facet667 key0 key763 rowPose763 = true := by decide +kernel
theorem row763_generated : rootPair 763 = some rowPose763 :=
  pairFieldsMatchB_sound (by decide) row763_fields
theorem row763_source : sourceKey 763 ∈ geometry.profile (sourceOwner 763) := by decide +kernel
theorem row763_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 555 key8).FastValid geometry rowPose763 := by decide +kernel
theorem row763_illegal : ¬ geometry.LegalContact rowPose763 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row763_reject_checked)
theorem row763_classified : RowClassified 763 := by
  intro p generated legal
  have he : rowPose763 = p := Option.some.inj (row763_generated.symm.trans generated)
  subst p
  exact (row763_illegal legal).elim

def rowPose764 : Pose 7 := ⟨perm24, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row764_fields : pairFieldsMatchB 188160 facet0 facet667 key0 key764 rowPose764 = true := by decide +kernel
theorem row764_generated : rootPair 764 = some rowPose764 :=
  pairFieldsMatchB_sound (by decide) row764_fields
theorem row764_source : sourceKey 764 ∈ geometry.profile (sourceOwner 764) := by decide +kernel
theorem row764_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 667 key0).FastValid geometry rowPose764 := by decide +kernel
theorem row764_illegal : ¬ geometry.LegalContact rowPose764 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row764_reject_checked)
theorem row764_classified : RowClassified 764 := by
  intro p generated legal
  have he : rowPose764 = p := Option.some.inj (row764_generated.symm.trans generated)
  subst p
  exact (row764_illegal legal).elim

def rowPose765 : Pose 7 := ⟨perm21, ![false, true, false, false, true, true, true], ![-1, 2, -1, -1, 2, 2, 2]⟩
theorem row765_fields : pairFieldsMatchB 188160 facet0 facet668 key0 key765 rowPose765 = true := by decide +kernel
theorem row765_generated : rootPair 765 = some rowPose765 :=
  pairFieldsMatchB_sound (by decide) row765_fields
theorem row765_source : sourceKey 765 ∈ geometry.profile (sourceOwner 765) := by decide +kernel
theorem row765_reject_checked : (show IndexedRejection 7 896 from .overlap ![0, 0, 0, 0, 1, 0, 0]).FastValid geometry rowPose765 := by decide +kernel
theorem row765_illegal : ¬ geometry.LegalContact rowPose765 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row765_reject_checked)
theorem row765_classified : RowClassified 765 := by
  intro p generated legal
  have he : rowPose765 = p := Option.some.inj (row765_generated.symm.trans generated)
  subst p
  exact (row765_illegal legal).elim

def rowPose766 : Pose 7 := ⟨perm37, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row766_fields : pairFieldsMatchB 188160 facet0 facet669 key0 key766 rowPose766 = true := by decide +kernel
theorem row766_generated : rootPair 766 = some rowPose766 :=
  pairFieldsMatchB_sound (by decide) row766_fields
theorem row766_source : sourceKey 766 ∈ geometry.profile (sourceOwner 766) := by decide +kernel
theorem row766_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 669 key1).FastValid geometry rowPose766 := by decide +kernel
theorem row766_illegal : ¬ geometry.LegalContact rowPose766 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row766_reject_checked)
theorem row766_classified : RowClassified 766 := by
  intro p generated legal
  have he : rowPose766 = p := Option.some.inj (row766_generated.symm.trans generated)
  subst p
  exact (row766_illegal legal).elim

def rowPose767 : Pose 7 := ⟨perm58, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row767_fields : pairFieldsMatchB 188160 facet0 facet670 key0 key767 rowPose767 = true := by decide +kernel
theorem row767_generated : rootPair 767 = some rowPose767 :=
  pairFieldsMatchB_sound (by decide) row767_fields
theorem row767_source : sourceKey 767 ∈ geometry.profile (sourceOwner 767) := by decide +kernel
theorem row767_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 670 key1).FastValid geometry rowPose767 := by decide +kernel
theorem row767_illegal : ¬ geometry.LegalContact rowPose767 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row767_reject_checked)
theorem row767_classified : RowClassified 767 := by
  intro p generated legal
  have he : rowPose767 = p := Option.some.inj (row767_generated.symm.trans generated)
  subst p
  exact (row767_illegal legal).elim

theorem chunk23_classified (i : Fin 32) : RowClassified ⟨736 + i.val, by omega⟩ := by
  fin_cases i
  · exact row736_classified
  · exact row737_classified
  · exact row738_classified
  · exact row739_classified
  · exact row740_classified
  · exact row741_classified
  · exact row742_classified
  · exact row743_classified
  · exact row744_classified
  · exact row745_classified
  · exact row746_classified
  · exact row747_classified
  · exact row748_classified
  · exact row749_classified
  · exact row750_classified
  · exact row751_classified
  · exact row752_classified
  · exact row753_classified
  · exact row754_classified
  · exact row755_classified
  · exact row756_classified
  · exact row757_classified
  · exact row758_classified
  · exact row759_classified
  · exact row760_classified
  · exact row761_classified
  · exact row762_classified
  · exact row763_classified
  · exact row764_classified
  · exact row765_classified
  · exact row766_classified
  · exact row767_classified

theorem chunk23_source (i : Fin 32) : sourceKey ⟨736 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨736 + i.val, by omega⟩) := by
  fin_cases i
  · exact row736_source
  · exact row737_source
  · exact row738_source
  · exact row739_source
  · exact row740_source
  · exact row741_source
  · exact row742_source
  · exact row743_source
  · exact row744_source
  · exact row745_source
  · exact row746_source
  · exact row747_source
  · exact row748_source
  · exact row749_source
  · exact row750_source
  · exact row751_source
  · exact row752_source
  · exact row753_source
  · exact row754_source
  · exact row755_source
  · exact row756_source
  · exact row757_source
  · exact row758_source
  · exact row759_source
  · exact row760_source
  · exact row761_source
  · exact row762_source
  · exact row763_source
  · exact row764_source
  · exact row765_source
  · exact row766_source
  · exact row767_source

#print axioms chunk23_classified
end SparseMonotiles.Contact.RootZeroPilot7
