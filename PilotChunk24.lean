module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose768 : Pose 7 := ⟨perm71, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row768_fields : pairFieldsMatchB 188160 facet0 facet671 key0 key768 rowPose768 = true := by decide +kernel
theorem row768_generated : rootPair 768 = some rowPose768 :=
  pairFieldsMatchB_sound (by decide) row768_fields
theorem row768_source : sourceKey 768 ∈ geometry.profile (sourceOwner 768) := by decide +kernel
theorem row768_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 671 key0).FastValid geometry rowPose768 := by decide +kernel
theorem row768_illegal : ¬ geometry.LegalContact rowPose768 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row768_reject_checked)
theorem row768_classified : RowClassified 768 := by
  intro p generated legal
  have he : rowPose768 = p := Option.some.inj (row768_generated.symm.trans generated)
  subst p
  exact (row768_illegal legal).elim

def rowPose769 : Pose 7 := ⟨perm95, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row769_fields : pairFieldsMatchB 188160 facet0 facet672 key0 key769 rowPose769 = true := by decide +kernel
theorem row769_generated : rootPair 769 = some rowPose769 :=
  pairFieldsMatchB_sound (by decide) row769_fields
theorem row769_source : sourceKey 769 ∈ geometry.profile (sourceOwner 769) := by decide +kernel
theorem row769_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 672 key1).FastValid geometry rowPose769 := by decide +kernel
theorem row769_illegal : ¬ geometry.LegalContact rowPose769 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row769_reject_checked)
theorem row769_classified : RowClassified 769 := by
  intro p generated legal
  have he : rowPose769 = p := Option.some.inj (row769_generated.symm.trans generated)
  subst p
  exact (row769_illegal legal).elim

def rowPose770 : Pose 7 := ⟨perm111, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row770_fields : pairFieldsMatchB 188160 facet0 facet673 key0 key770 rowPose770 = true := by decide +kernel
theorem row770_generated : rootPair 770 = some rowPose770 :=
  pairFieldsMatchB_sound (by decide) row770_fields
theorem row770_source : sourceKey 770 ∈ geometry.profile (sourceOwner 770) := by decide +kernel
theorem row770_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 673 key0).FastValid geometry rowPose770 := by decide +kernel
theorem row770_illegal : ¬ geometry.LegalContact rowPose770 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row770_reject_checked)
theorem row770_classified : RowClassified 770 := by
  intro p generated legal
  have he : rowPose770 = p := Option.some.inj (row770_generated.symm.trans generated)
  subst p
  exact (row770_illegal legal).elim

def rowPose771 : Pose 7 := ⟨perm10, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row771_fields : pairFieldsMatchB 188160 facet0 facet674 key0 key771 rowPose771 = true := by decide +kernel
theorem row771_generated : rootPair 771 = some rowPose771 :=
  pairFieldsMatchB_sound (by decide) row771_fields
theorem row771_source : sourceKey 771 ∈ geometry.profile (sourceOwner 771) := by decide +kernel
theorem row771_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 674 key0).FastValid geometry rowPose771 := by decide +kernel
theorem row771_illegal : ¬ geometry.LegalContact rowPose771 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row771_reject_checked)
theorem row771_classified : RowClassified 771 := by
  intro p generated legal
  have he : rowPose771 = p := Option.some.inj (row771_generated.symm.trans generated)
  subst p
  exact (row771_illegal legal).elim

def rowPose772 : Pose 7 := ⟨perm22, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row772_fields : pairFieldsMatchB 188160 facet0 facet675 key0 key772 rowPose772 = true := by decide +kernel
theorem row772_generated : rootPair 772 = some rowPose772 :=
  pairFieldsMatchB_sound (by decide) row772_fields
theorem row772_source : sourceKey 772 ∈ geometry.profile (sourceOwner 772) := by decide +kernel
theorem row772_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 675 key1).FastValid geometry rowPose772 := by decide +kernel
theorem row772_illegal : ¬ geometry.LegalContact rowPose772 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row772_reject_checked)
theorem row772_classified : RowClassified 772 := by
  intro p generated legal
  have he : rowPose772 = p := Option.some.inj (row772_generated.symm.trans generated)
  subst p
  exact (row772_illegal legal).elim

def rowPose773 : Pose 7 := ⟨perm37, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row773_fields : pairFieldsMatchB 188160 facet0 facet676 key0 key773 rowPose773 = true := by decide +kernel
theorem row773_generated : rootPair 773 = some rowPose773 :=
  pairFieldsMatchB_sound (by decide) row773_fields
theorem row773_source : sourceKey 773 ∈ geometry.profile (sourceOwner 773) := by decide +kernel
theorem row773_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 676 key0).FastValid geometry rowPose773 := by decide +kernel
theorem row773_illegal : ¬ geometry.LegalContact rowPose773 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row773_reject_checked)
theorem row773_classified : RowClassified 773 := by
  intro p generated legal
  have he : rowPose773 = p := Option.some.inj (row773_generated.symm.trans generated)
  subst p
  exact (row773_illegal legal).elim

def rowPose774 : Pose 7 := ⟨perm58, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row774_fields : pairFieldsMatchB 188160 facet0 facet677 key0 key774 rowPose774 = true := by decide +kernel
theorem row774_generated : rootPair 774 = some rowPose774 :=
  pairFieldsMatchB_sound (by decide) row774_fields
theorem row774_source : sourceKey 774 ∈ geometry.profile (sourceOwner 774) := by decide +kernel
theorem row774_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 677 key0).FastValid geometry rowPose774 := by decide +kernel
theorem row774_illegal : ¬ geometry.LegalContact rowPose774 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row774_reject_checked)
theorem row774_classified : RowClassified 774 := by
  intro p generated legal
  have he : rowPose774 = p := Option.some.inj (row774_generated.symm.trans generated)
  subst p
  exact (row774_illegal legal).elim

def rowPose775 : Pose 7 := ⟨perm74, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row775_fields : pairFieldsMatchB 188160 facet0 facet678 key0 key775 rowPose775 = true := by decide +kernel
theorem row775_generated : rootPair 775 = some rowPose775 :=
  pairFieldsMatchB_sound (by decide) row775_fields
theorem row775_source : sourceKey 775 ∈ geometry.profile (sourceOwner 775) := by decide +kernel
theorem row775_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 678 key0).FastValid geometry rowPose775 := by decide +kernel
theorem row775_illegal : ¬ geometry.LegalContact rowPose775 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row775_reject_checked)
theorem row775_classified : RowClassified 775 := by
  intro p generated legal
  have he : rowPose775 = p := Option.some.inj (row775_generated.symm.trans generated)
  subst p
  exact (row775_illegal legal).elim

def rowPose776 : Pose 7 := ⟨perm69, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row776_fields : pairFieldsMatchB 188160 facet0 facet678 key0 key776 rowPose776 = true := by decide +kernel
theorem row776_generated : rootPair 776 = some rowPose776 :=
  pairFieldsMatchB_sound (by decide) row776_fields
theorem row776_source : sourceKey 776 ∈ geometry.profile (sourceOwner 776) := by decide +kernel
theorem row776_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 692 key8).FastValid geometry rowPose776 := by decide +kernel
theorem row776_illegal : ¬ geometry.LegalContact rowPose776 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row776_reject_checked)
theorem row776_classified : RowClassified 776 := by
  intro p generated legal
  have he : rowPose776 = p := Option.some.inj (row776_generated.symm.trans generated)
  subst p
  exact (row776_illegal legal).elim

def rowPose777 : Pose 7 := ⟨perm87, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row777_fields : pairFieldsMatchB 188160 facet0 facet679 key0 key777 rowPose777 = true := by decide +kernel
theorem row777_generated : rootPair 777 = some rowPose777 :=
  pairFieldsMatchB_sound (by decide) row777_fields
theorem row777_source : sourceKey 777 ∈ geometry.profile (sourceOwner 777) := by decide +kernel
theorem row777_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 679 key1).FastValid geometry rowPose777 := by decide +kernel
theorem row777_illegal : ¬ geometry.LegalContact rowPose777 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row777_reject_checked)
theorem row777_classified : RowClassified 777 := by
  intro p generated legal
  have he : rowPose777 = p := Option.some.inj (row777_generated.symm.trans generated)
  subst p
  exact (row777_illegal legal).elim

def rowPose778 : Pose 7 := ⟨perm96, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row778_fields : pairFieldsMatchB 188160 facet0 facet680 key0 key778 rowPose778 = true := by decide +kernel
theorem row778_generated : rootPair 778 = some rowPose778 :=
  pairFieldsMatchB_sound (by decide) row778_fields
theorem row778_source : sourceKey 778 ∈ geometry.profile (sourceOwner 778) := by decide +kernel
theorem row778_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 680 key1).FastValid geometry rowPose778 := by decide +kernel
theorem row778_illegal : ¬ geometry.LegalContact rowPose778 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row778_reject_checked)
theorem row778_classified : RowClassified 778 := by
  intro p generated legal
  have he : rowPose778 = p := Option.some.inj (row778_generated.symm.trans generated)
  subst p
  exact (row778_illegal legal).elim

def rowPose779 : Pose 7 := ⟨perm0, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row779_fields : pairFieldsMatchB 188160 facet0 facet681 key0 key779 rowPose779 = true := by decide +kernel
theorem row779_generated : rootPair 779 = some rowPose779 :=
  pairFieldsMatchB_sound (by decide) row779_fields
theorem row779_source : sourceKey 779 ∈ geometry.profile (sourceOwner 779) := by decide +kernel
theorem row779_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 674 key8).FastValid geometry rowPose779 := by decide +kernel
theorem row779_illegal : ¬ geometry.LegalContact rowPose779 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row779_reject_checked)
theorem row779_classified : RowClassified 779 := by
  intro p generated legal
  have he : rowPose779 = p := Option.some.inj (row779_generated.symm.trans generated)
  subst p
  exact (row779_illegal legal).elim

def rowPose780 : Pose 7 := ⟨perm15, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row780_fields : pairFieldsMatchB 188160 facet0 facet681 key0 key780 rowPose780 = true := by decide +kernel
theorem row780_generated : rootPair 780 = some rowPose780 :=
  pairFieldsMatchB_sound (by decide) row780_fields
theorem row780_source : sourceKey 780 ∈ geometry.profile (sourceOwner 780) := by decide +kernel
theorem row780_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 681 key0).FastValid geometry rowPose780 := by decide +kernel
theorem row780_illegal : ¬ geometry.LegalContact rowPose780 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row780_reject_checked)
theorem row780_classified : RowClassified 780 := by
  intro p generated legal
  have he : rowPose780 = p := Option.some.inj (row780_generated.symm.trans generated)
  subst p
  exact (row780_illegal legal).elim

def rowPose781 : Pose 7 := ⟨perm21, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row781_fields : pairFieldsMatchB 188160 facet0 facet682 key0 key781 rowPose781 = true := by decide +kernel
theorem row781_generated : rootPair 781 = some rowPose781 :=
  pairFieldsMatchB_sound (by decide) row781_fields
theorem row781_source : sourceKey 781 ∈ geometry.profile (sourceOwner 781) := by decide +kernel
theorem row781_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 682 key0).FastValid geometry rowPose781 := by decide +kernel
theorem row781_illegal : ¬ geometry.LegalContact rowPose781 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row781_reject_checked)
theorem row781_classified : RowClassified 781 := by
  intro p generated legal
  have he : rowPose781 = p := Option.some.inj (row781_generated.symm.trans generated)
  subst p
  exact (row781_illegal legal).elim

def rowPose782 : Pose 7 := ⟨perm42, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row782_fields : pairFieldsMatchB 188160 facet0 facet683 key0 key782 rowPose782 = true := by decide +kernel
theorem row782_generated : rootPair 782 = some rowPose782 :=
  pairFieldsMatchB_sound (by decide) row782_fields
theorem row782_source : sourceKey 782 ∈ geometry.profile (sourceOwner 782) := by decide +kernel
theorem row782_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 683 key0).FastValid geometry rowPose782 := by decide +kernel
theorem row782_illegal : ¬ geometry.LegalContact rowPose782 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row782_reject_checked)
theorem row782_classified : RowClassified 782 := by
  intro p generated legal
  have he : rowPose782 = p := Option.some.inj (row782_generated.symm.trans generated)
  subst p
  exact (row782_illegal legal).elim

def rowPose783 : Pose 7 := ⟨perm55, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row783_fields : pairFieldsMatchB 188160 facet0 facet684 key0 key783 rowPose783 = true := by decide +kernel
theorem row783_generated : rootPair 783 = some rowPose783 :=
  pairFieldsMatchB_sound (by decide) row783_fields
theorem row783_source : sourceKey 783 ∈ geometry.profile (sourceOwner 783) := by decide +kernel
theorem row783_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 684 key1).FastValid geometry rowPose783 := by decide +kernel
theorem row783_illegal : ¬ geometry.LegalContact rowPose783 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row783_reject_checked)
theorem row783_classified : RowClassified 783 := by
  intro p generated legal
  have he : rowPose783 = p := Option.some.inj (row783_generated.symm.trans generated)
  subst p
  exact (row783_illegal legal).elim

def rowPose784 : Pose 7 := ⟨perm73, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row784_fields : pairFieldsMatchB 188160 facet0 facet685 key0 key784 rowPose784 = true := by decide +kernel
theorem row784_generated : rootPair 784 = some rowPose784 :=
  pairFieldsMatchB_sound (by decide) row784_fields
theorem row784_source : sourceKey 784 ∈ geometry.profile (sourceOwner 784) := by decide +kernel
theorem row784_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 685 key0).FastValid geometry rowPose784 := by decide +kernel
theorem row784_illegal : ¬ geometry.LegalContact rowPose784 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row784_reject_checked)
theorem row784_classified : RowClassified 784 := by
  intro p generated legal
  have he : rowPose784 = p := Option.some.inj (row784_generated.symm.trans generated)
  subst p
  exact (row784_illegal legal).elim

def rowPose785 : Pose 7 := ⟨perm87, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row785_fields : pairFieldsMatchB 188160 facet0 facet686 key0 key785 rowPose785 = true := by decide +kernel
theorem row785_generated : rootPair 785 = some rowPose785 :=
  pairFieldsMatchB_sound (by decide) row785_fields
theorem row785_source : sourceKey 785 ∈ geometry.profile (sourceOwner 785) := by decide +kernel
theorem row785_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 686 key1).FastValid geometry rowPose785 := by decide +kernel
theorem row785_illegal : ¬ geometry.LegalContact rowPose785 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row785_reject_checked)
theorem row785_classified : RowClassified 785 := by
  intro p generated legal
  have he : rowPose785 = p := Option.some.inj (row785_generated.symm.trans generated)
  subst p
  exact (row785_illegal legal).elim

def rowPose786 : Pose 7 := ⟨perm96, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row786_fields : pairFieldsMatchB 188160 facet0 facet687 key0 key786 rowPose786 = true := by decide +kernel
theorem row786_generated : rootPair 786 = some rowPose786 :=
  pairFieldsMatchB_sound (by decide) row786_fields
theorem row786_source : sourceKey 786 ∈ geometry.profile (sourceOwner 786) := by decide +kernel
theorem row786_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 687 key1).FastValid geometry rowPose786 := by decide +kernel
theorem row786_illegal : ¬ geometry.LegalContact rowPose786 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row786_reject_checked)
theorem row786_classified : RowClassified 786 := by
  intro p generated legal
  have he : rowPose786 = p := Option.some.inj (row786_generated.symm.trans generated)
  subst p
  exact (row786_illegal legal).elim

def rowPose787 : Pose 7 := ⟨perm15, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row787_fields : pairFieldsMatchB 188160 facet0 facet688 key0 key787 rowPose787 = true := by decide +kernel
theorem row787_generated : rootPair 787 = some rowPose787 :=
  pairFieldsMatchB_sound (by decide) row787_fields
theorem row787_source : sourceKey 787 ∈ geometry.profile (sourceOwner 787) := by decide +kernel
theorem row787_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 688 key1).FastValid geometry rowPose787 := by decide +kernel
theorem row787_illegal : ¬ geometry.LegalContact rowPose787 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row787_reject_checked)
theorem row787_classified : RowClassified 787 := by
  intro p generated legal
  have he : rowPose787 = p := Option.some.inj (row787_generated.symm.trans generated)
  subst p
  exact (row787_illegal legal).elim

def rowPose788 : Pose 7 := ⟨perm24, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row788_fields : pairFieldsMatchB 188160 facet0 facet689 key0 key788 rowPose788 = true := by decide +kernel
theorem row788_generated : rootPair 788 = some rowPose788 :=
  pairFieldsMatchB_sound (by decide) row788_fields
theorem row788_source : sourceKey 788 ∈ geometry.profile (sourceOwner 788) := by decide +kernel
theorem row788_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 689 key1).FastValid geometry rowPose788 := by decide +kernel
theorem row788_illegal : ¬ geometry.LegalContact rowPose788 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row788_reject_checked)
theorem row788_classified : RowClassified 788 := by
  intro p generated legal
  have he : rowPose788 = p := Option.some.inj (row788_generated.symm.trans generated)
  subst p
  exact (row788_illegal legal).elim

def rowPose789 : Pose 7 := ⟨perm37, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row789_fields : pairFieldsMatchB 188160 facet0 facet690 key0 key789 rowPose789 = true := by decide +kernel
theorem row789_generated : rootPair 789 = some rowPose789 :=
  pairFieldsMatchB_sound (by decide) row789_fields
theorem row789_source : sourceKey 789 ∈ geometry.profile (sourceOwner 789) := by decide +kernel
theorem row789_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 690 key0).FastValid geometry rowPose789 := by decide +kernel
theorem row789_illegal : ¬ geometry.LegalContact rowPose789 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row789_reject_checked)
theorem row789_classified : RowClassified 789 := by
  intro p generated legal
  have he : rowPose789 = p := Option.some.inj (row789_generated.symm.trans generated)
  subst p
  exact (row789_illegal legal).elim

def rowPose790 : Pose 7 := ⟨perm42, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row790_fields : pairFieldsMatchB 188160 facet0 facet690 key0 key790 rowPose790 = true := by decide +kernel
theorem row790_generated : rootPair 790 = some rowPose790 :=
  pairFieldsMatchB_sound (by decide) row790_fields
theorem row790_source : sourceKey 790 ∈ geometry.profile (sourceOwner 790) := by decide +kernel
theorem row790_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 465 key8).FastValid geometry rowPose790 := by decide +kernel
theorem row790_illegal : ¬ geometry.LegalContact rowPose790 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row790_reject_checked)
theorem row790_classified : RowClassified 790 := by
  intro p generated legal
  have he : rowPose790 = p := Option.some.inj (row790_generated.symm.trans generated)
  subst p
  exact (row790_illegal legal).elim

def rowPose791 : Pose 7 := ⟨perm53, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row791_fields : pairFieldsMatchB 188160 facet0 facet691 key0 key791 rowPose791 = true := by decide +kernel
theorem row791_generated : rootPair 791 = some rowPose791 :=
  pairFieldsMatchB_sound (by decide) row791_fields
theorem row791_source : sourceKey 791 ∈ geometry.profile (sourceOwner 791) := by decide +kernel
theorem row791_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 691 key0).FastValid geometry rowPose791 := by decide +kernel
theorem row791_illegal : ¬ geometry.LegalContact rowPose791 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row791_reject_checked)
theorem row791_classified : RowClassified 791 := by
  intro p generated legal
  have he : rowPose791 = p := Option.some.inj (row791_generated.symm.trans generated)
  subst p
  exact (row791_illegal legal).elim

def rowPose792 : Pose 7 := ⟨perm74, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row792_fields : pairFieldsMatchB 188160 facet0 facet692 key0 key792 rowPose792 = true := by decide +kernel
theorem row792_generated : rootPair 792 = some rowPose792 :=
  pairFieldsMatchB_sound (by decide) row792_fields
theorem row792_source : sourceKey 792 ∈ geometry.profile (sourceOwner 792) := by decide +kernel
theorem row792_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 692 key0).FastValid geometry rowPose792 := by decide +kernel
theorem row792_illegal : ¬ geometry.LegalContact rowPose792 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row792_reject_checked)
theorem row792_classified : RowClassified 792 := by
  intro p generated legal
  have he : rowPose792 = p := Option.some.inj (row792_generated.symm.trans generated)
  subst p
  exact (row792_illegal legal).elim

def rowPose793 : Pose 7 := ⟨perm89, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row793_fields : pairFieldsMatchB 188160 facet0 facet693 key0 key793 rowPose793 = true := by decide +kernel
theorem row793_generated : rootPair 793 = some rowPose793 :=
  pairFieldsMatchB_sound (by decide) row793_fields
theorem row793_source : sourceKey 793 ∈ geometry.profile (sourceOwner 793) := by decide +kernel
theorem row793_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 693 key1).FastValid geometry rowPose793 := by decide +kernel
theorem row793_illegal : ¬ geometry.LegalContact rowPose793 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row793_reject_checked)
theorem row793_classified : RowClassified 793 := by
  intro p generated legal
  have he : rowPose793 = p := Option.some.inj (row793_generated.symm.trans generated)
  subst p
  exact (row793_illegal legal).elim

def rowPose794 : Pose 7 := ⟨perm101, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row794_fields : pairFieldsMatchB 188160 facet0 facet694 key0 key794 rowPose794 = true := by decide +kernel
theorem row794_generated : rootPair 794 = some rowPose794 :=
  pairFieldsMatchB_sound (by decide) row794_fields
theorem row794_source : sourceKey 794 ∈ geometry.profile (sourceOwner 794) := by decide +kernel
theorem row794_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 694 key0).FastValid geometry rowPose794 := by decide +kernel
theorem row794_illegal : ¬ geometry.LegalContact rowPose794 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row794_reject_checked)
theorem row794_classified : RowClassified 794 := by
  intro p generated legal
  have he : rowPose794 = p := Option.some.inj (row794_generated.symm.trans generated)
  subst p
  exact (row794_illegal legal).elim

def rowPose795 : Pose 7 := ⟨perm5, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row795_fields : pairFieldsMatchB 188160 facet0 facet695 key0 key795 rowPose795 = true := by decide +kernel
theorem row795_generated : rootPair 795 = some rowPose795 :=
  pairFieldsMatchB_sound (by decide) row795_fields
theorem row795_source : sourceKey 795 ∈ geometry.profile (sourceOwner 795) := by decide +kernel
theorem row795_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 695 key1).FastValid geometry rowPose795 := by decide +kernel
theorem row795_illegal : ¬ geometry.LegalContact rowPose795 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row795_reject_checked)
theorem row795_classified : RowClassified 795 := by
  intro p generated legal
  have he : rowPose795 = p := Option.some.inj (row795_generated.symm.trans generated)
  subst p
  exact (row795_illegal legal).elim

def rowPose796 : Pose 7 := ⟨perm21, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row796_fields : pairFieldsMatchB 188160 facet0 facet696 key0 key796 rowPose796 = true := by decide +kernel
theorem row796_generated : rootPair 796 = some rowPose796 :=
  pairFieldsMatchB_sound (by decide) row796_fields
theorem row796_source : sourceKey 796 ∈ geometry.profile (sourceOwner 796) := by decide +kernel
theorem row796_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 696 key0).FastValid geometry rowPose796 := by decide +kernel
theorem row796_illegal : ¬ geometry.LegalContact rowPose796 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row796_reject_checked)
theorem row796_classified : RowClassified 796 := by
  intro p generated legal
  have he : rowPose796 = p := Option.some.inj (row796_generated.symm.trans generated)
  subst p
  exact (row796_illegal legal).elim

def rowPose797 : Pose 7 := ⟨perm42, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row797_fields : pairFieldsMatchB 188160 facet0 facet697 key0 key797 rowPose797 = true := by decide +kernel
theorem row797_generated : rootPair 797 = some rowPose797 :=
  pairFieldsMatchB_sound (by decide) row797_fields
theorem row797_source : sourceKey 797 ∈ geometry.profile (sourceOwner 797) := by decide +kernel
theorem row797_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 697 key0).FastValid geometry rowPose797 := by decide +kernel
theorem row797_illegal : ¬ geometry.LegalContact rowPose797 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row797_reject_checked)
theorem row797_classified : RowClassified 797 := by
  intro p generated legal
  have he : rowPose797 = p := Option.some.inj (row797_generated.symm.trans generated)
  subst p
  exact (row797_illegal legal).elim

def rowPose798 : Pose 7 := ⟨perm53, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row798_fields : pairFieldsMatchB 188160 facet0 facet698 key0 key798 rowPose798 = true := by decide +kernel
theorem row798_generated : rootPair 798 = some rowPose798 :=
  pairFieldsMatchB_sound (by decide) row798_fields
theorem row798_source : sourceKey 798 ∈ geometry.profile (sourceOwner 798) := by decide +kernel
theorem row798_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 726 key8).FastValid geometry rowPose798 := by decide +kernel
theorem row798_illegal : ¬ geometry.LegalContact rowPose798 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row798_reject_checked)
theorem row798_classified : RowClassified 798 := by
  intro p generated legal
  have he : rowPose798 = p := Option.some.inj (row798_generated.symm.trans generated)
  subst p
  exact (row798_illegal legal).elim

def rowPose799 : Pose 7 := ⟨perm58, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row799_fields : pairFieldsMatchB 188160 facet0 facet698 key0 key799 rowPose799 = true := by decide +kernel
theorem row799_generated : rootPair 799 = some rowPose799 :=
  pairFieldsMatchB_sound (by decide) row799_fields
theorem row799_source : sourceKey 799 ∈ geometry.profile (sourceOwner 799) := by decide +kernel
theorem row799_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 698 key0).FastValid geometry rowPose799 := by decide +kernel
theorem row799_illegal : ¬ geometry.LegalContact rowPose799 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row799_reject_checked)
theorem row799_classified : RowClassified 799 := by
  intro p generated legal
  have he : rowPose799 = p := Option.some.inj (row799_generated.symm.trans generated)
  subst p
  exact (row799_illegal legal).elim

theorem chunk24_classified (i : Fin 32) : RowClassified ⟨768 + i.val, by omega⟩ := by
  fin_cases i
  · exact row768_classified
  · exact row769_classified
  · exact row770_classified
  · exact row771_classified
  · exact row772_classified
  · exact row773_classified
  · exact row774_classified
  · exact row775_classified
  · exact row776_classified
  · exact row777_classified
  · exact row778_classified
  · exact row779_classified
  · exact row780_classified
  · exact row781_classified
  · exact row782_classified
  · exact row783_classified
  · exact row784_classified
  · exact row785_classified
  · exact row786_classified
  · exact row787_classified
  · exact row788_classified
  · exact row789_classified
  · exact row790_classified
  · exact row791_classified
  · exact row792_classified
  · exact row793_classified
  · exact row794_classified
  · exact row795_classified
  · exact row796_classified
  · exact row797_classified
  · exact row798_classified
  · exact row799_classified

theorem chunk24_source (i : Fin 32) : sourceKey ⟨768 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨768 + i.val, by omega⟩) := by
  fin_cases i
  · exact row768_source
  · exact row769_source
  · exact row770_source
  · exact row771_source
  · exact row772_source
  · exact row773_source
  · exact row774_source
  · exact row775_source
  · exact row776_source
  · exact row777_source
  · exact row778_source
  · exact row779_source
  · exact row780_source
  · exact row781_source
  · exact row782_source
  · exact row783_source
  · exact row784_source
  · exact row785_source
  · exact row786_source
  · exact row787_source
  · exact row788_source
  · exact row789_source
  · exact row790_source
  · exact row791_source
  · exact row792_source
  · exact row793_source
  · exact row794_source
  · exact row795_source
  · exact row796_source
  · exact row797_source
  · exact row798_source
  · exact row799_source

#print axioms chunk24_classified
end SparseMonotiles.Contact.RootZeroPilot7
