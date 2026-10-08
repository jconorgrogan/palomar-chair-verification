module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose800 : Pose 7 := ⟨perm69, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row800_fields : pairFieldsMatchB 188160 facet0 facet699 key0 key800 rowPose800 = true := by decide +kernel
theorem row800_generated : rootPair 800 = some rowPose800 :=
  pairFieldsMatchB_sound (by decide) row800_fields
theorem row800_source : sourceKey 800 ∈ geometry.profile (sourceOwner 800) := by decide +kernel
theorem row800_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 699 key1).FastValid geometry rowPose800 := by decide +kernel
theorem row800_illegal : ¬ geometry.LegalContact rowPose800 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row800_reject_checked)
theorem row800_classified : RowClassified 800 := by
  intro p generated legal
  have he : rowPose800 = p := Option.some.inj (row800_generated.symm.trans generated)
  subst p
  exact (row800_illegal legal).elim

def rowPose801 : Pose 7 := ⟨perm90, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row801_fields : pairFieldsMatchB 188160 facet0 facet700 key0 key801 rowPose801 = true := by decide +kernel
theorem row801_generated : rootPair 801 = some rowPose801 :=
  pairFieldsMatchB_sound (by decide) row801_fields
theorem row801_source : sourceKey 801 ∈ geometry.profile (sourceOwner 801) := by decide +kernel
theorem row801_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 700 key1).FastValid geometry rowPose801 := by decide +kernel
theorem row801_illegal : ¬ geometry.LegalContact rowPose801 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row801_reject_checked)
theorem row801_classified : RowClassified 801 := by
  intro p generated legal
  have he : rowPose801 = p := Option.some.inj (row801_generated.symm.trans generated)
  subst p
  exact (row801_illegal legal).elim

def rowPose802 : Pose 7 := ⟨perm106, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row802_fields : pairFieldsMatchB 188160 facet0 facet701 key0 key802 rowPose802 = true := by decide +kernel
theorem row802_generated : rootPair 802 = some rowPose802 :=
  pairFieldsMatchB_sound (by decide) row802_fields
theorem row802_source : sourceKey 802 ∈ geometry.profile (sourceOwner 802) := by decide +kernel
theorem row802_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 701 key0).FastValid geometry rowPose802 := by decide +kernel
theorem row802_illegal : ¬ geometry.LegalContact rowPose802 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row802_reject_checked)
theorem row802_classified : RowClassified 802 := by
  intro p generated legal
  have he : rowPose802 = p := Option.some.inj (row802_generated.symm.trans generated)
  subst p
  exact (row802_illegal legal).elim

def rowPose803 : Pose 7 := ⟨perm10, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row803_fields : pairFieldsMatchB 188160 facet0 facet702 key0 key803 rowPose803 = true := by decide +kernel
theorem row803_generated : rootPair 803 = some rowPose803 :=
  pairFieldsMatchB_sound (by decide) row803_fields
theorem row803_source : sourceKey 803 ∈ geometry.profile (sourceOwner 803) := by decide +kernel
theorem row803_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 702 key1).FastValid geometry rowPose803 := by decide +kernel
theorem row803_illegal : ¬ geometry.LegalContact rowPose803 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row803_reject_checked)
theorem row803_classified : RowClassified 803 := by
  intro p generated legal
  have he : rowPose803 = p := Option.some.inj (row803_generated.symm.trans generated)
  subst p
  exact (row803_illegal legal).elim

def rowPose804 : Pose 7 := ⟨perm22, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row804_fields : pairFieldsMatchB 188160 facet0 facet703 key0 key804 rowPose804 = true := by decide +kernel
theorem row804_generated : rootPair 804 = some rowPose804 :=
  pairFieldsMatchB_sound (by decide) row804_fields
theorem row804_source : sourceKey 804 ∈ geometry.profile (sourceOwner 804) := by decide +kernel
theorem row804_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 703 key0).FastValid geometry rowPose804 := by decide +kernel
theorem row804_illegal : ¬ geometry.LegalContact rowPose804 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row804_reject_checked)
theorem row804_classified : RowClassified 804 := by
  intro p generated legal
  have he : rowPose804 = p := Option.some.inj (row804_generated.symm.trans generated)
  subst p
  exact (row804_illegal legal).elim

def rowPose805 : Pose 7 := ⟨perm37, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row805_fields : pairFieldsMatchB 188160 facet0 facet704 key0 key805 rowPose805 = true := by decide +kernel
theorem row805_generated : rootPair 805 = some rowPose805 :=
  pairFieldsMatchB_sound (by decide) row805_fields
theorem row805_source : sourceKey 805 ∈ geometry.profile (sourceOwner 805) := by decide +kernel
theorem row805_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 704 key1).FastValid geometry rowPose805 := by decide +kernel
theorem row805_illegal : ¬ geometry.LegalContact rowPose805 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row805_reject_checked)
theorem row805_classified : RowClassified 805 := by
  intro p generated legal
  have he : rowPose805 = p := Option.some.inj (row805_generated.symm.trans generated)
  subst p
  exact (row805_illegal legal).elim

def rowPose806 : Pose 7 := ⟨perm58, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row806_fields : pairFieldsMatchB 188160 facet0 facet705 key0 key806 rowPose806 = true := by decide +kernel
theorem row806_generated : rootPair 806 = some rowPose806 :=
  pairFieldsMatchB_sound (by decide) row806_fields
theorem row806_source : sourceKey 806 ∈ geometry.profile (sourceOwner 806) := by decide +kernel
theorem row806_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 705 key1).FastValid geometry rowPose806 := by decide +kernel
theorem row806_illegal : ¬ geometry.LegalContact rowPose806 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row806_reject_checked)
theorem row806_classified : RowClassified 806 := by
  intro p generated legal
  have he : rowPose806 = p := Option.some.inj (row806_generated.symm.trans generated)
  subst p
  exact (row806_illegal legal).elim

def rowPose807 : Pose 7 := ⟨perm74, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row807_fields : pairFieldsMatchB 188160 facet0 facet706 key0 key807 rowPose807 = true := by decide +kernel
theorem row807_generated : rootPair 807 = some rowPose807 :=
  pairFieldsMatchB_sound (by decide) row807_fields
theorem row807_source : sourceKey 807 ∈ geometry.profile (sourceOwner 807) := by decide +kernel
theorem row807_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 762 key8).FastValid geometry rowPose807 := by decide +kernel
theorem row807_illegal : ¬ geometry.LegalContact rowPose807 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row807_reject_checked)
theorem row807_classified : RowClassified 807 := by
  intro p generated legal
  have he : rowPose807 = p := Option.some.inj (row807_generated.symm.trans generated)
  subst p
  exact (row807_illegal legal).elim

def rowPose808 : Pose 7 := ⟨perm69, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row808_fields : pairFieldsMatchB 188160 facet0 facet706 key0 key808 rowPose808 = true := by decide +kernel
theorem row808_generated : rootPair 808 = some rowPose808 :=
  pairFieldsMatchB_sound (by decide) row808_fields
theorem row808_source : sourceKey 808 ∈ geometry.profile (sourceOwner 808) := by decide +kernel
theorem row808_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 706 key0).FastValid geometry rowPose808 := by decide +kernel
theorem row808_illegal : ¬ geometry.LegalContact rowPose808 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row808_reject_checked)
theorem row808_classified : RowClassified 808 := by
  intro p generated legal
  have he : rowPose808 = p := Option.some.inj (row808_generated.symm.trans generated)
  subst p
  exact (row808_illegal legal).elim

def rowPose809 : Pose 7 := ⟨perm87, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row809_fields : pairFieldsMatchB 188160 facet0 facet707 key0 key809 rowPose809 = true := by decide +kernel
theorem row809_generated : rootPair 809 = some rowPose809 :=
  pairFieldsMatchB_sound (by decide) row809_fields
theorem row809_source : sourceKey 809 ∈ geometry.profile (sourceOwner 809) := by decide +kernel
theorem row809_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 707 key0).FastValid geometry rowPose809 := by decide +kernel
theorem row809_illegal : ¬ geometry.LegalContact rowPose809 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row809_reject_checked)
theorem row809_classified : RowClassified 809 := by
  intro p generated legal
  have he : rowPose809 = p := Option.some.inj (row809_generated.symm.trans generated)
  subst p
  exact (row809_illegal legal).elim

def rowPose810 : Pose 7 := ⟨perm96, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row810_fields : pairFieldsMatchB 188160 facet0 facet708 key0 key810 rowPose810 = true := by decide +kernel
theorem row810_generated : rootPair 810 = some rowPose810 :=
  pairFieldsMatchB_sound (by decide) row810_fields
theorem row810_source : sourceKey 810 ∈ geometry.profile (sourceOwner 810) := by decide +kernel
theorem row810_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 708 key0).FastValid geometry rowPose810 := by decide +kernel
theorem row810_illegal : ¬ geometry.LegalContact rowPose810 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row810_reject_checked)
theorem row810_classified : RowClassified 810 := by
  intro p generated legal
  have he : rowPose810 = p := Option.some.inj (row810_generated.symm.trans generated)
  subst p
  exact (row810_illegal legal).elim

def rowPose811 : Pose 7 := ⟨perm0, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row811_fields : pairFieldsMatchB 188160 facet0 facet709 key0 key811 rowPose811 = true := by decide +kernel
theorem row811_generated : rootPair 811 = some rowPose811 :=
  pairFieldsMatchB_sound (by decide) row811_fields
theorem row811_source : sourceKey 811 ∈ geometry.profile (sourceOwner 811) := by decide +kernel
theorem row811_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 709 key0).FastValid geometry rowPose811 := by decide +kernel
theorem row811_illegal : ¬ geometry.LegalContact rowPose811 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row811_reject_checked)
theorem row811_classified : RowClassified 811 := by
  intro p generated legal
  have he : rowPose811 = p := Option.some.inj (row811_generated.symm.trans generated)
  subst p
  exact (row811_illegal legal).elim

def rowPose812 : Pose 7 := ⟨perm21, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row812_fields : pairFieldsMatchB 188160 facet0 facet710 key0 key812 rowPose812 = true := by decide +kernel
theorem row812_generated : rootPair 812 = some rowPose812 :=
  pairFieldsMatchB_sound (by decide) row812_fields
theorem row812_source : sourceKey 812 ∈ geometry.profile (sourceOwner 812) := by decide +kernel
theorem row812_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 823 key8).FastValid geometry rowPose812 := by decide +kernel
theorem row812_illegal : ¬ geometry.LegalContact rowPose812 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row812_reject_checked)
theorem row812_classified : RowClassified 812 := by
  intro p generated legal
  have he : rowPose812 = p := Option.some.inj (row812_generated.symm.trans generated)
  subst p
  exact (row812_illegal legal).elim

def rowPose813 : Pose 7 := ⟨perm24, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row813_fields : pairFieldsMatchB 188160 facet0 facet710 key0 key813 rowPose813 = true := by decide +kernel
theorem row813_generated : rootPair 813 = some rowPose813 :=
  pairFieldsMatchB_sound (by decide) row813_fields
theorem row813_source : sourceKey 813 ∈ geometry.profile (sourceOwner 813) := by decide +kernel
theorem row813_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 710 key0).FastValid geometry rowPose813 := by decide +kernel
theorem row813_illegal : ¬ geometry.LegalContact rowPose813 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row813_reject_checked)
theorem row813_classified : RowClassified 813 := by
  intro p generated legal
  have he : rowPose813 = p := Option.some.inj (row813_generated.symm.trans generated)
  subst p
  exact (row813_illegal legal).elim

def rowPose814 : Pose 7 := ⟨perm37, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row814_fields : pairFieldsMatchB 188160 facet0 facet711 key0 key814 rowPose814 = true := by decide +kernel
theorem row814_generated : rootPair 814 = some rowPose814 :=
  pairFieldsMatchB_sound (by decide) row814_fields
theorem row814_source : sourceKey 814 ∈ geometry.profile (sourceOwner 814) := by decide +kernel
theorem row814_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 711 key1).FastValid geometry rowPose814 := by decide +kernel
theorem row814_illegal : ¬ geometry.LegalContact rowPose814 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row814_reject_checked)
theorem row814_classified : RowClassified 814 := by
  intro p generated legal
  have he : rowPose814 = p := Option.some.inj (row814_generated.symm.trans generated)
  subst p
  exact (row814_illegal legal).elim

def rowPose815 : Pose 7 := ⟨perm58, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row815_fields : pairFieldsMatchB 188160 facet0 facet712 key0 key815 rowPose815 = true := by decide +kernel
theorem row815_generated : rootPair 815 = some rowPose815 :=
  pairFieldsMatchB_sound (by decide) row815_fields
theorem row815_source : sourceKey 815 ∈ geometry.profile (sourceOwner 815) := by decide +kernel
theorem row815_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 712 key1).FastValid geometry rowPose815 := by decide +kernel
theorem row815_illegal : ¬ geometry.LegalContact rowPose815 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row815_reject_checked)
theorem row815_classified : RowClassified 815 := by
  intro p generated legal
  have he : rowPose815 = p := Option.some.inj (row815_generated.symm.trans generated)
  subst p
  exact (row815_illegal legal).elim

def rowPose816 : Pose 7 := ⟨perm71, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row816_fields : pairFieldsMatchB 188160 facet0 facet713 key0 key816 rowPose816 = true := by decide +kernel
theorem row816_generated : rootPair 816 = some rowPose816 :=
  pairFieldsMatchB_sound (by decide) row816_fields
theorem row816_source : sourceKey 816 ∈ geometry.profile (sourceOwner 816) := by decide +kernel
theorem row816_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 713 key0).FastValid geometry rowPose816 := by decide +kernel
theorem row816_illegal : ¬ geometry.LegalContact rowPose816 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row816_reject_checked)
theorem row816_classified : RowClassified 816 := by
  intro p generated legal
  have he : rowPose816 = p := Option.some.inj (row816_generated.symm.trans generated)
  subst p
  exact (row816_illegal legal).elim

def rowPose817 : Pose 7 := ⟨perm95, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row817_fields : pairFieldsMatchB 188160 facet0 facet714 key0 key817 rowPose817 = true := by decide +kernel
theorem row817_generated : rootPair 817 = some rowPose817 :=
  pairFieldsMatchB_sound (by decide) row817_fields
theorem row817_source : sourceKey 817 ∈ geometry.profile (sourceOwner 817) := by decide +kernel
theorem row817_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 714 key1).FastValid geometry rowPose817 := by decide +kernel
theorem row817_illegal : ¬ geometry.LegalContact rowPose817 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row817_reject_checked)
theorem row817_classified : RowClassified 817 := by
  intro p generated legal
  have he : rowPose817 = p := Option.some.inj (row817_generated.symm.trans generated)
  subst p
  exact (row817_illegal legal).elim

def rowPose818 : Pose 7 := ⟨perm111, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row818_fields : pairFieldsMatchB 188160 facet0 facet715 key0 key818 rowPose818 = true := by decide +kernel
theorem row818_generated : rootPair 818 = some rowPose818 :=
  pairFieldsMatchB_sound (by decide) row818_fields
theorem row818_source : sourceKey 818 ∈ geometry.profile (sourceOwner 818) := by decide +kernel
theorem row818_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 715 key0).FastValid geometry rowPose818 := by decide +kernel
theorem row818_illegal : ¬ geometry.LegalContact rowPose818 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row818_reject_checked)
theorem row818_classified : RowClassified 818 := by
  intro p generated legal
  have he : rowPose818 = p := Option.some.inj (row818_generated.symm.trans generated)
  subst p
  exact (row818_illegal legal).elim

def rowPose819 : Pose 7 := ⟨perm15, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row819_fields : pairFieldsMatchB 188160 facet0 facet716 key0 key819 rowPose819 = true := by decide +kernel
theorem row819_generated : rootPair 819 = some rowPose819 :=
  pairFieldsMatchB_sound (by decide) row819_fields
theorem row819_source : sourceKey 819 ∈ geometry.profile (sourceOwner 819) := by decide +kernel
theorem row819_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 716 key1).FastValid geometry rowPose819 := by decide +kernel
theorem row819_illegal : ¬ geometry.LegalContact rowPose819 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row819_reject_checked)
theorem row819_classified : RowClassified 819 := by
  intro p generated legal
  have he : rowPose819 = p := Option.some.inj (row819_generated.symm.trans generated)
  subst p
  exact (row819_illegal legal).elim

def rowPose820 : Pose 7 := ⟨perm24, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row820_fields : pairFieldsMatchB 188160 facet0 facet717 key0 key820 rowPose820 = true := by decide +kernel
theorem row820_generated : rootPair 820 = some rowPose820 :=
  pairFieldsMatchB_sound (by decide) row820_fields
theorem row820_source : sourceKey 820 ∈ geometry.profile (sourceOwner 820) := by decide +kernel
theorem row820_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 717 key1).FastValid geometry rowPose820 := by decide +kernel
theorem row820_illegal : ¬ geometry.LegalContact rowPose820 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row820_reject_checked)
theorem row820_classified : RowClassified 820 := by
  intro p generated legal
  have he : rowPose820 = p := Option.some.inj (row820_generated.symm.trans generated)
  subst p
  exact (row820_illegal legal).elim

def rowPose821 : Pose 7 := ⟨perm38, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row821_fields : pairFieldsMatchB 188160 facet0 facet718 key0 key821 rowPose821 = true := by decide +kernel
theorem row821_generated : rootPair 821 = some rowPose821 :=
  pairFieldsMatchB_sound (by decide) row821_fields
theorem row821_source : sourceKey 821 ∈ geometry.profile (sourceOwner 821) := by decide +kernel
theorem row821_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 718 key0).FastValid geometry rowPose821 := by decide +kernel
theorem row821_illegal : ¬ geometry.LegalContact rowPose821 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row821_reject_checked)
theorem row821_classified : RowClassified 821 := by
  intro p generated legal
  have he : rowPose821 = p := Option.some.inj (row821_generated.symm.trans generated)
  subst p
  exact (row821_illegal legal).elim

def rowPose822 : Pose 7 := ⟨perm56, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row822_fields : pairFieldsMatchB 188160 facet0 facet719 key0 key822 rowPose822 = true := by decide +kernel
theorem row822_generated : rootPair 822 = some rowPose822 :=
  pairFieldsMatchB_sound (by decide) row822_fields
theorem row822_source : sourceKey 822 ∈ geometry.profile (sourceOwner 822) := by decide +kernel
theorem row822_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 719 key1).FastValid geometry rowPose822 := by decide +kernel
theorem row822_illegal : ¬ geometry.LegalContact rowPose822 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row822_reject_checked)
theorem row822_classified : RowClassified 822 := by
  intro p generated legal
  have he : rowPose822 = p := Option.some.inj (row822_generated.symm.trans generated)
  subst p
  exact (row822_illegal legal).elim

def rowPose823 : Pose 7 := ⟨perm69, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row823_fields : pairFieldsMatchB 188160 facet0 facet720 key0 key823 rowPose823 = true := by decide +kernel
theorem row823_generated : rootPair 823 = some rowPose823 :=
  pairFieldsMatchB_sound (by decide) row823_fields
theorem row823_source : sourceKey 823 ∈ geometry.profile (sourceOwner 823) := by decide +kernel
theorem row823_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 720 key0).FastValid geometry rowPose823 := by decide +kernel
theorem row823_illegal : ¬ geometry.LegalContact rowPose823 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row823_reject_checked)
theorem row823_classified : RowClassified 823 := by
  intro p generated legal
  have he : rowPose823 = p := Option.some.inj (row823_generated.symm.trans generated)
  subst p
  exact (row823_illegal legal).elim

def rowPose824 : Pose 7 := ⟨perm90, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row824_fields : pairFieldsMatchB 188160 facet0 facet721 key0 key824 rowPose824 = true := by decide +kernel
theorem row824_generated : rootPair 824 = some rowPose824 :=
  pairFieldsMatchB_sound (by decide) row824_fields
theorem row824_source : sourceKey 824 ∈ geometry.profile (sourceOwner 824) := by decide +kernel
theorem row824_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 721 key0).FastValid geometry rowPose824 := by decide +kernel
theorem row824_illegal : ¬ geometry.LegalContact rowPose824 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row824_reject_checked)
theorem row824_classified : RowClassified 824 := by
  intro p generated legal
  have he : rowPose824 = p := Option.some.inj (row824_generated.symm.trans generated)
  subst p
  exact (row824_illegal legal).elim

def rowPose825 : Pose 7 := ⟨perm96, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row825_fields : pairFieldsMatchB 188160 facet0 facet722 key0 key825 rowPose825 = true := by decide +kernel
theorem row825_generated : rootPair 825 = some rowPose825 :=
  pairFieldsMatchB_sound (by decide) row825_fields
theorem row825_source : sourceKey 825 ∈ geometry.profile (sourceOwner 825) := by decide +kernel
theorem row825_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 722 key0).FastValid geometry rowPose825 := by decide +kernel
theorem row825_illegal : ¬ geometry.LegalContact rowPose825 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row825_reject_checked)
theorem row825_classified : RowClassified 825 := by
  intro p generated legal
  have he : rowPose825 = p := Option.some.inj (row825_generated.symm.trans generated)
  subst p
  exact (row825_illegal legal).elim

def rowPose826 : Pose 7 := ⟨perm111, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row826_fields : pairFieldsMatchB 188160 facet0 facet722 key0 key826 rowPose826 = true := by decide +kernel
theorem row826_generated : rootPair 826 = some rowPose826 :=
  pairFieldsMatchB_sound (by decide) row826_fields
theorem row826_source : sourceKey 826 ∈ geometry.profile (sourceOwner 826) := by decide +kernel
theorem row826_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 272 key8).FastValid geometry rowPose826 := by decide +kernel
theorem row826_illegal : ¬ geometry.LegalContact rowPose826 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row826_reject_checked)
theorem row826_classified : RowClassified 826 := by
  intro p generated legal
  have he : rowPose826 = p := Option.some.inj (row826_generated.symm.trans generated)
  subst p
  exact (row826_illegal legal).elim

def rowPose827 : Pose 7 := ⟨perm15, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row827_fields : pairFieldsMatchB 188160 facet0 facet723 key0 key827 rowPose827 = true := by decide +kernel
theorem row827_generated : rootPair 827 = some rowPose827 :=
  pairFieldsMatchB_sound (by decide) row827_fields
theorem row827_source : sourceKey 827 ∈ geometry.profile (sourceOwner 827) := by decide +kernel
theorem row827_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 723 key0).FastValid geometry rowPose827 := by decide +kernel
theorem row827_illegal : ¬ geometry.LegalContact rowPose827 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row827_reject_checked)
theorem row827_classified : RowClassified 827 := by
  intro p generated legal
  have he : rowPose827 = p := Option.some.inj (row827_generated.symm.trans generated)
  subst p
  exact (row827_illegal legal).elim

def rowPose828 : Pose 7 := ⟨perm24, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row828_fields : pairFieldsMatchB 188160 facet0 facet724 key0 key828 rowPose828 = true := by decide +kernel
theorem row828_generated : rootPair 828 = some rowPose828 :=
  pairFieldsMatchB_sound (by decide) row828_fields
theorem row828_source : sourceKey 828 ∈ geometry.profile (sourceOwner 828) := by decide +kernel
theorem row828_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 724 key0).FastValid geometry rowPose828 := by decide +kernel
theorem row828_illegal : ¬ geometry.LegalContact rowPose828 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row828_reject_checked)
theorem row828_classified : RowClassified 828 := by
  intro p generated legal
  have he : rowPose828 = p := Option.some.inj (row828_generated.symm.trans generated)
  subst p
  exact (row828_illegal legal).elim

def rowPose829 : Pose 7 := ⟨perm38, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row829_fields : pairFieldsMatchB 188160 facet0 facet725 key0 key829 rowPose829 = true := by decide +kernel
theorem row829_generated : rootPair 829 = some rowPose829 :=
  pairFieldsMatchB_sound (by decide) row829_fields
theorem row829_source : sourceKey 829 ∈ geometry.profile (sourceOwner 829) := by decide +kernel
theorem row829_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 725 key1).FastValid geometry rowPose829 := by decide +kernel
theorem row829_illegal : ¬ geometry.LegalContact rowPose829 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row829_reject_checked)
theorem row829_classified : RowClassified 829 := by
  intro p generated legal
  have he : rowPose829 = p := Option.some.inj (row829_generated.symm.trans generated)
  subst p
  exact (row829_illegal legal).elim

def rowPose830 : Pose 7 := ⟨perm56, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row830_fields : pairFieldsMatchB 188160 facet0 facet726 key0 key830 rowPose830 = true := by decide +kernel
theorem row830_generated : rootPair 830 = some rowPose830 :=
  pairFieldsMatchB_sound (by decide) row830_fields
theorem row830_source : sourceKey 830 ∈ geometry.profile (sourceOwner 830) := by decide +kernel
theorem row830_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 726 key0).FastValid geometry rowPose830 := by decide +kernel
theorem row830_illegal : ¬ geometry.LegalContact rowPose830 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row830_reject_checked)
theorem row830_classified : RowClassified 830 := by
  intro p generated legal
  have he : rowPose830 = p := Option.some.inj (row830_generated.symm.trans generated)
  subst p
  exact (row830_illegal legal).elim

def rowPose831 : Pose 7 := ⟨perm69, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row831_fields : pairFieldsMatchB 188160 facet0 facet727 key0 key831 rowPose831 = true := by decide +kernel
theorem row831_generated : rootPair 831 = some rowPose831 :=
  pairFieldsMatchB_sound (by decide) row831_fields
theorem row831_source : sourceKey 831 ∈ geometry.profile (sourceOwner 831) := by decide +kernel
theorem row831_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 727 key1).FastValid geometry rowPose831 := by decide +kernel
theorem row831_illegal : ¬ geometry.LegalContact rowPose831 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row831_reject_checked)
theorem row831_classified : RowClassified 831 := by
  intro p generated legal
  have he : rowPose831 = p := Option.some.inj (row831_generated.symm.trans generated)
  subst p
  exact (row831_illegal legal).elim

theorem chunk25_classified (i : Fin 32) : RowClassified ⟨800 + i.val, by omega⟩ := by
  fin_cases i
  · exact row800_classified
  · exact row801_classified
  · exact row802_classified
  · exact row803_classified
  · exact row804_classified
  · exact row805_classified
  · exact row806_classified
  · exact row807_classified
  · exact row808_classified
  · exact row809_classified
  · exact row810_classified
  · exact row811_classified
  · exact row812_classified
  · exact row813_classified
  · exact row814_classified
  · exact row815_classified
  · exact row816_classified
  · exact row817_classified
  · exact row818_classified
  · exact row819_classified
  · exact row820_classified
  · exact row821_classified
  · exact row822_classified
  · exact row823_classified
  · exact row824_classified
  · exact row825_classified
  · exact row826_classified
  · exact row827_classified
  · exact row828_classified
  · exact row829_classified
  · exact row830_classified
  · exact row831_classified

theorem chunk25_source (i : Fin 32) : sourceKey ⟨800 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨800 + i.val, by omega⟩) := by
  fin_cases i
  · exact row800_source
  · exact row801_source
  · exact row802_source
  · exact row803_source
  · exact row804_source
  · exact row805_source
  · exact row806_source
  · exact row807_source
  · exact row808_source
  · exact row809_source
  · exact row810_source
  · exact row811_source
  · exact row812_source
  · exact row813_source
  · exact row814_source
  · exact row815_source
  · exact row816_source
  · exact row817_source
  · exact row818_source
  · exact row819_source
  · exact row820_source
  · exact row821_source
  · exact row822_source
  · exact row823_source
  · exact row824_source
  · exact row825_source
  · exact row826_source
  · exact row827_source
  · exact row828_source
  · exact row829_source
  · exact row830_source
  · exact row831_source

#print axioms chunk25_classified
end SparseMonotiles.Contact.RootZeroPilot7
