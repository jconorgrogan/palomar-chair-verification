module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose832 : Pose 7 := ⟨perm90, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row832_fields : pairFieldsMatchB 188160 facet0 facet728 key0 key832 rowPose832 = true := by decide +kernel
theorem row832_generated : rootPair 832 = some rowPose832 :=
  pairFieldsMatchB_sound (by decide) row832_fields
theorem row832_source : sourceKey 832 ∈ geometry.profile (sourceOwner 832) := by decide +kernel
theorem row832_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 728 key1).FastValid geometry rowPose832 := by decide +kernel
theorem row832_illegal : ¬ geometry.LegalContact rowPose832 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row832_reject_checked)
theorem row832_classified : RowClassified 832 := by
  intro p generated legal
  have he : rowPose832 = p := Option.some.inj (row832_generated.symm.trans generated)
  subst p
  exact (row832_illegal legal).elim

def rowPose833 : Pose 7 := ⟨perm96, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row833_fields : pairFieldsMatchB 188160 facet0 facet729 key0 key833 rowPose833 = true := by decide +kernel
theorem row833_generated : rootPair 833 = some rowPose833 :=
  pairFieldsMatchB_sound (by decide) row833_fields
theorem row833_source : sourceKey 833 ∈ geometry.profile (sourceOwner 833) := by decide +kernel
theorem row833_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 715 key8).FastValid geometry rowPose833 := by decide +kernel
theorem row833_illegal : ¬ geometry.LegalContact rowPose833 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row833_reject_checked)
theorem row833_classified : RowClassified 833 := by
  intro p generated legal
  have he : rowPose833 = p := Option.some.inj (row833_generated.symm.trans generated)
  subst p
  exact (row833_illegal legal).elim

def rowPose834 : Pose 7 := ⟨perm111, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row834_fields : pairFieldsMatchB 188160 facet0 facet729 key0 key834 rowPose834 = true := by decide +kernel
theorem row834_generated : rootPair 834 = some rowPose834 :=
  pairFieldsMatchB_sound (by decide) row834_fields
theorem row834_source : sourceKey 834 ∈ geometry.profile (sourceOwner 834) := by decide +kernel
theorem row834_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 729 key0).FastValid geometry rowPose834 := by decide +kernel
theorem row834_illegal : ¬ geometry.LegalContact rowPose834 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row834_reject_checked)
theorem row834_classified : RowClassified 834 := by
  intro p generated legal
  have he : rowPose834 = p := Option.some.inj (row834_generated.symm.trans generated)
  subst p
  exact (row834_illegal legal).elim

def rowPose835 : Pose 7 := ⟨perm15, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row835_fields : pairFieldsMatchB 188160 facet0 facet730 key0 key835 rowPose835 = true := by decide +kernel
theorem row835_generated : rootPair 835 = some rowPose835 :=
  pairFieldsMatchB_sound (by decide) row835_fields
theorem row835_source : sourceKey 835 ∈ geometry.profile (sourceOwner 835) := by decide +kernel
theorem row835_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 730 key0).FastValid geometry rowPose835 := by decide +kernel
theorem row835_illegal : ¬ geometry.LegalContact rowPose835 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row835_reject_checked)
theorem row835_classified : RowClassified 835 := by
  intro p generated legal
  have he : rowPose835 = p := Option.some.inj (row835_generated.symm.trans generated)
  subst p
  exact (row835_illegal legal).elim

def rowPose836 : Pose 7 := ⟨perm24, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row836_fields : pairFieldsMatchB 188160 facet0 facet731 key0 key836 rowPose836 = true := by decide +kernel
theorem row836_generated : rootPair 836 = some rowPose836 :=
  pairFieldsMatchB_sound (by decide) row836_fields
theorem row836_source : sourceKey 836 ∈ geometry.profile (sourceOwner 836) := by decide +kernel
theorem row836_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 731 key0).FastValid geometry rowPose836 := by decide +kernel
theorem row836_illegal : ¬ geometry.LegalContact rowPose836 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row836_reject_checked)
theorem row836_classified : RowClassified 836 := by
  intro p generated legal
  have he : rowPose836 = p := Option.some.inj (row836_generated.symm.trans generated)
  subst p
  exact (row836_illegal legal).elim

def rowPose837 : Pose 7 := ⟨perm38, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row837_fields : pairFieldsMatchB 188160 facet0 facet732 key0 key837 rowPose837 = true := by decide +kernel
theorem row837_generated : rootPair 837 = some rowPose837 :=
  pairFieldsMatchB_sound (by decide) row837_fields
theorem row837_source : sourceKey 837 ∈ geometry.profile (sourceOwner 837) := by decide +kernel
theorem row837_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 732 key1).FastValid geometry rowPose837 := by decide +kernel
theorem row837_illegal : ¬ geometry.LegalContact rowPose837 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row837_reject_checked)
theorem row837_classified : RowClassified 837 := by
  intro p generated legal
  have he : rowPose837 = p := Option.some.inj (row837_generated.symm.trans generated)
  subst p
  exact (row837_illegal legal).elim

def rowPose838 : Pose 7 := ⟨perm56, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row838_fields : pairFieldsMatchB 188160 facet0 facet733 key0 key838 rowPose838 = true := by decide +kernel
theorem row838_generated : rootPair 838 = some rowPose838 :=
  pairFieldsMatchB_sound (by decide) row838_fields
theorem row838_source : sourceKey 838 ∈ geometry.profile (sourceOwner 838) := by decide +kernel
theorem row838_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 733 key0).FastValid geometry rowPose838 := by decide +kernel
theorem row838_illegal : ¬ geometry.LegalContact rowPose838 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row838_reject_checked)
theorem row838_classified : RowClassified 838 := by
  intro p generated legal
  have he : rowPose838 = p := Option.some.inj (row838_generated.symm.trans generated)
  subst p
  exact (row838_illegal legal).elim

def rowPose839 : Pose 7 := ⟨perm69, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row839_fields : pairFieldsMatchB 188160 facet0 facet734 key0 key839 rowPose839 = true := by decide +kernel
theorem row839_generated : rootPair 839 = some rowPose839 :=
  pairFieldsMatchB_sound (by decide) row839_fields
theorem row839_source : sourceKey 839 ∈ geometry.profile (sourceOwner 839) := by decide +kernel
theorem row839_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 734 key1).FastValid geometry rowPose839 := by decide +kernel
theorem row839_illegal : ¬ geometry.LegalContact rowPose839 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row839_reject_checked)
theorem row839_classified : RowClassified 839 := by
  intro p generated legal
  have he : rowPose839 = p := Option.some.inj (row839_generated.symm.trans generated)
  subst p
  exact (row839_illegal legal).elim

def rowPose840 : Pose 7 := ⟨perm90, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row840_fields : pairFieldsMatchB 188160 facet0 facet735 key0 key840 rowPose840 = true := by decide +kernel
theorem row840_generated : rootPair 840 = some rowPose840 :=
  pairFieldsMatchB_sound (by decide) row840_fields
theorem row840_source : sourceKey 840 ∈ geometry.profile (sourceOwner 840) := by decide +kernel
theorem row840_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 735 key1).FastValid geometry rowPose840 := by decide +kernel
theorem row840_illegal : ¬ geometry.LegalContact rowPose840 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row840_reject_checked)
theorem row840_classified : RowClassified 840 := by
  intro p generated legal
  have he : rowPose840 = p := Option.some.inj (row840_generated.symm.trans generated)
  subst p
  exact (row840_illegal legal).elim

def rowPose841 : Pose 7 := ⟨perm96, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row841_fields : pairFieldsMatchB 188160 facet0 facet736 key0 key841 rowPose841 = true := by decide +kernel
theorem row841_generated : rootPair 841 = some rowPose841 :=
  pairFieldsMatchB_sound (by decide) row841_fields
theorem row841_source : sourceKey 841 ∈ geometry.profile (sourceOwner 841) := by decide +kernel
theorem row841_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 750 key8).FastValid geometry rowPose841 := by decide +kernel
theorem row841_illegal : ¬ geometry.LegalContact rowPose841 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row841_reject_checked)
theorem row841_classified : RowClassified 841 := by
  intro p generated legal
  have he : rowPose841 = p := Option.some.inj (row841_generated.symm.trans generated)
  subst p
  exact (row841_illegal legal).elim

def rowPose842 : Pose 7 := ⟨perm111, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row842_fields : pairFieldsMatchB 188160 facet0 facet736 key0 key842 rowPose842 = true := by decide +kernel
theorem row842_generated : rootPair 842 = some rowPose842 :=
  pairFieldsMatchB_sound (by decide) row842_fields
theorem row842_source : sourceKey 842 ∈ geometry.profile (sourceOwner 842) := by decide +kernel
theorem row842_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 736 key0).FastValid geometry rowPose842 := by decide +kernel
theorem row842_illegal : ¬ geometry.LegalContact rowPose842 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row842_reject_checked)
theorem row842_classified : RowClassified 842 := by
  intro p generated legal
  have he : rowPose842 = p := Option.some.inj (row842_generated.symm.trans generated)
  subst p
  exact (row842_illegal legal).elim

def rowPose843 : Pose 7 := ⟨perm15, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row843_fields : pairFieldsMatchB 188160 facet0 facet737 key0 key843 rowPose843 = true := by decide +kernel
theorem row843_generated : rootPair 843 = some rowPose843 :=
  pairFieldsMatchB_sound (by decide) row843_fields
theorem row843_source : sourceKey 843 ∈ geometry.profile (sourceOwner 843) := by decide +kernel
theorem row843_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 737 key1).FastValid geometry rowPose843 := by decide +kernel
theorem row843_illegal : ¬ geometry.LegalContact rowPose843 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row843_reject_checked)
theorem row843_classified : RowClassified 843 := by
  intro p generated legal
  have he : rowPose843 = p := Option.some.inj (row843_generated.symm.trans generated)
  subst p
  exact (row843_illegal legal).elim

def rowPose844 : Pose 7 := ⟨perm24, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row844_fields : pairFieldsMatchB 188160 facet0 facet738 key0 key844 rowPose844 = true := by decide +kernel
theorem row844_generated : rootPair 844 = some rowPose844 :=
  pairFieldsMatchB_sound (by decide) row844_fields
theorem row844_source : sourceKey 844 ∈ geometry.profile (sourceOwner 844) := by decide +kernel
theorem row844_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 738 key1).FastValid geometry rowPose844 := by decide +kernel
theorem row844_illegal : ¬ geometry.LegalContact rowPose844 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row844_reject_checked)
theorem row844_classified : RowClassified 844 := by
  intro p generated legal
  have he : rowPose844 = p := Option.some.inj (row844_generated.symm.trans generated)
  subst p
  exact (row844_illegal legal).elim

def rowPose845 : Pose 7 := ⟨perm38, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row845_fields : pairFieldsMatchB 188160 facet0 facet739 key0 key845 rowPose845 = true := by decide +kernel
theorem row845_generated : rootPair 845 = some rowPose845 :=
  pairFieldsMatchB_sound (by decide) row845_fields
theorem row845_source : sourceKey 845 ∈ geometry.profile (sourceOwner 845) := by decide +kernel
theorem row845_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 739 key0).FastValid geometry rowPose845 := by decide +kernel
theorem row845_illegal : ¬ geometry.LegalContact rowPose845 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row845_reject_checked)
theorem row845_classified : RowClassified 845 := by
  intro p generated legal
  have he : rowPose845 = p := Option.some.inj (row845_generated.symm.trans generated)
  subst p
  exact (row845_illegal legal).elim

def rowPose846 : Pose 7 := ⟨perm56, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row846_fields : pairFieldsMatchB 188160 facet0 facet740 key0 key846 rowPose846 = true := by decide +kernel
theorem row846_generated : rootPair 846 = some rowPose846 :=
  pairFieldsMatchB_sound (by decide) row846_fields
theorem row846_source : sourceKey 846 ∈ geometry.profile (sourceOwner 846) := by decide +kernel
theorem row846_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 740 key1).FastValid geometry rowPose846 := by decide +kernel
theorem row846_illegal : ¬ geometry.LegalContact rowPose846 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row846_reject_checked)
theorem row846_classified : RowClassified 846 := by
  intro p generated legal
  have he : rowPose846 = p := Option.some.inj (row846_generated.symm.trans generated)
  subst p
  exact (row846_illegal legal).elim

def rowPose847 : Pose 7 := ⟨perm69, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row847_fields : pairFieldsMatchB 188160 facet0 facet741 key0 key847 rowPose847 = true := by decide +kernel
theorem row847_generated : rootPair 847 = some rowPose847 :=
  pairFieldsMatchB_sound (by decide) row847_fields
theorem row847_source : sourceKey 847 ∈ geometry.profile (sourceOwner 847) := by decide +kernel
theorem row847_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 741 key0).FastValid geometry rowPose847 := by decide +kernel
theorem row847_illegal : ¬ geometry.LegalContact rowPose847 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row847_reject_checked)
theorem row847_classified : RowClassified 847 := by
  intro p generated legal
  have he : rowPose847 = p := Option.some.inj (row847_generated.symm.trans generated)
  subst p
  exact (row847_illegal legal).elim

def rowPose848 : Pose 7 := ⟨perm90, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row848_fields : pairFieldsMatchB 188160 facet0 facet742 key0 key848 rowPose848 = true := by decide +kernel
theorem row848_generated : rootPair 848 = some rowPose848 :=
  pairFieldsMatchB_sound (by decide) row848_fields
theorem row848_source : sourceKey 848 ∈ geometry.profile (sourceOwner 848) := by decide +kernel
theorem row848_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 742 key0).FastValid geometry rowPose848 := by decide +kernel
theorem row848_illegal : ¬ geometry.LegalContact rowPose848 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row848_reject_checked)
theorem row848_classified : RowClassified 848 := by
  intro p generated legal
  have he : rowPose848 = p := Option.some.inj (row848_generated.symm.trans generated)
  subst p
  exact (row848_illegal legal).elim

def rowPose849 : Pose 7 := ⟨perm96, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row849_fields : pairFieldsMatchB 188160 facet0 facet743 key0 key849 rowPose849 = true := by decide +kernel
theorem row849_generated : rootPair 849 = some rowPose849 :=
  pairFieldsMatchB_sound (by decide) row849_fields
theorem row849_source : sourceKey 849 ∈ geometry.profile (sourceOwner 849) := by decide +kernel
theorem row849_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 743 key0).FastValid geometry rowPose849 := by decide +kernel
theorem row849_illegal : ¬ geometry.LegalContact rowPose849 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row849_reject_checked)
theorem row849_classified : RowClassified 849 := by
  intro p generated legal
  have he : rowPose849 = p := Option.some.inj (row849_generated.symm.trans generated)
  subst p
  exact (row849_illegal legal).elim

def rowPose850 : Pose 7 := ⟨perm111, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row850_fields : pairFieldsMatchB 188160 facet0 facet743 key0 key850 rowPose850 = true := by decide +kernel
theorem row850_generated : rootPair 850 = some rowPose850 :=
  pairFieldsMatchB_sound (by decide) row850_fields
theorem row850_source : sourceKey 850 ∈ geometry.profile (sourceOwner 850) := by decide +kernel
theorem row850_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 293 key8).FastValid geometry rowPose850 := by decide +kernel
theorem row850_illegal : ¬ geometry.LegalContact rowPose850 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row850_reject_checked)
theorem row850_classified : RowClassified 850 := by
  intro p generated legal
  have he : rowPose850 = p := Option.some.inj (row850_generated.symm.trans generated)
  subst p
  exact (row850_illegal legal).elim

def rowPose851 : Pose 7 := ⟨perm10, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row851_fields : pairFieldsMatchB 188160 facet0 facet744 key0 key851 rowPose851 = true := by decide +kernel
theorem row851_generated : rootPair 851 = some rowPose851 :=
  pairFieldsMatchB_sound (by decide) row851_fields
theorem row851_source : sourceKey 851 ∈ geometry.profile (sourceOwner 851) := by decide +kernel
theorem row851_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 744 key0).FastValid geometry rowPose851 := by decide +kernel
theorem row851_illegal : ¬ geometry.LegalContact rowPose851 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row851_reject_checked)
theorem row851_classified : RowClassified 851 := by
  intro p generated legal
  have he : rowPose851 = p := Option.some.inj (row851_generated.symm.trans generated)
  subst p
  exact (row851_illegal legal).elim

def rowPose852 : Pose 7 := ⟨perm22, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row852_fields : pairFieldsMatchB 188160 facet0 facet745 key0 key852 rowPose852 = true := by decide +kernel
theorem row852_generated : rootPair 852 = some rowPose852 :=
  pairFieldsMatchB_sound (by decide) row852_fields
theorem row852_source : sourceKey 852 ∈ geometry.profile (sourceOwner 852) := by decide +kernel
theorem row852_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 745 key1).FastValid geometry rowPose852 := by decide +kernel
theorem row852_illegal : ¬ geometry.LegalContact rowPose852 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row852_reject_checked)
theorem row852_classified : RowClassified 852 := by
  intro p generated legal
  have he : rowPose852 = p := Option.some.inj (row852_generated.symm.trans generated)
  subst p
  exact (row852_illegal legal).elim

def rowPose853 : Pose 7 := ⟨perm37, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row853_fields : pairFieldsMatchB 188160 facet0 facet746 key0 key853 rowPose853 = true := by decide +kernel
theorem row853_generated : rootPair 853 = some rowPose853 :=
  pairFieldsMatchB_sound (by decide) row853_fields
theorem row853_source : sourceKey 853 ∈ geometry.profile (sourceOwner 853) := by decide +kernel
theorem row853_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 746 key0).FastValid geometry rowPose853 := by decide +kernel
theorem row853_illegal : ¬ geometry.LegalContact rowPose853 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row853_reject_checked)
theorem row853_classified : RowClassified 853 := by
  intro p generated legal
  have he : rowPose853 = p := Option.some.inj (row853_generated.symm.trans generated)
  subst p
  exact (row853_illegal legal).elim

def rowPose854 : Pose 7 := ⟨perm58, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row854_fields : pairFieldsMatchB 188160 facet0 facet747 key0 key854 rowPose854 = true := by decide +kernel
theorem row854_generated : rootPair 854 = some rowPose854 :=
  pairFieldsMatchB_sound (by decide) row854_fields
theorem row854_source : sourceKey 854 ∈ geometry.profile (sourceOwner 854) := by decide +kernel
theorem row854_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 747 key0).FastValid geometry rowPose854 := by decide +kernel
theorem row854_illegal : ¬ geometry.LegalContact rowPose854 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row854_reject_checked)
theorem row854_classified : RowClassified 854 := by
  intro p generated legal
  have he : rowPose854 = p := Option.some.inj (row854_generated.symm.trans generated)
  subst p
  exact (row854_illegal legal).elim

def rowPose855 : Pose 7 := ⟨perm74, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row855_fields : pairFieldsMatchB 188160 facet0 facet748 key0 key855 rowPose855 = true := by decide +kernel
theorem row855_generated : rootPair 855 = some rowPose855 :=
  pairFieldsMatchB_sound (by decide) row855_fields
theorem row855_source : sourceKey 855 ∈ geometry.profile (sourceOwner 855) := by decide +kernel
theorem row855_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 748 key0).FastValid geometry rowPose855 := by decide +kernel
theorem row855_illegal : ¬ geometry.LegalContact rowPose855 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row855_reject_checked)
theorem row855_classified : RowClassified 855 := by
  intro p generated legal
  have he : rowPose855 = p := Option.some.inj (row855_generated.symm.trans generated)
  subst p
  exact (row855_illegal legal).elim

def rowPose856 : Pose 7 := ⟨perm69, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row856_fields : pairFieldsMatchB 188160 facet0 facet748 key0 key856 rowPose856 = true := by decide +kernel
theorem row856_generated : rootPair 856 = some rowPose856 :=
  pairFieldsMatchB_sound (by decide) row856_fields
theorem row856_source : sourceKey 856 ∈ geometry.profile (sourceOwner 856) := by decide +kernel
theorem row856_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 734 key8).FastValid geometry rowPose856 := by decide +kernel
theorem row856_illegal : ¬ geometry.LegalContact rowPose856 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row856_reject_checked)
theorem row856_classified : RowClassified 856 := by
  intro p generated legal
  have he : rowPose856 = p := Option.some.inj (row856_generated.symm.trans generated)
  subst p
  exact (row856_illegal legal).elim

def rowPose857 : Pose 7 := ⟨perm87, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row857_fields : pairFieldsMatchB 188160 facet0 facet749 key0 key857 rowPose857 = true := by decide +kernel
theorem row857_generated : rootPair 857 = some rowPose857 :=
  pairFieldsMatchB_sound (by decide) row857_fields
theorem row857_source : sourceKey 857 ∈ geometry.profile (sourceOwner 857) := by decide +kernel
theorem row857_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 749 key1).FastValid geometry rowPose857 := by decide +kernel
theorem row857_illegal : ¬ geometry.LegalContact rowPose857 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row857_reject_checked)
theorem row857_classified : RowClassified 857 := by
  intro p generated legal
  have he : rowPose857 = p := Option.some.inj (row857_generated.symm.trans generated)
  subst p
  exact (row857_illegal legal).elim

def rowPose858 : Pose 7 := ⟨perm96, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row858_fields : pairFieldsMatchB 188160 facet0 facet750 key0 key858 rowPose858 = true := by decide +kernel
theorem row858_generated : rootPair 858 = some rowPose858 :=
  pairFieldsMatchB_sound (by decide) row858_fields
theorem row858_source : sourceKey 858 ∈ geometry.profile (sourceOwner 858) := by decide +kernel
theorem row858_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 750 key1).FastValid geometry rowPose858 := by decide +kernel
theorem row858_illegal : ¬ geometry.LegalContact rowPose858 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row858_reject_checked)
theorem row858_classified : RowClassified 858 := by
  intro p generated legal
  have he : rowPose858 = p := Option.some.inj (row858_generated.symm.trans generated)
  subst p
  exact (row858_illegal legal).elim

def rowPose859 : Pose 7 := ⟨perm5, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row859_fields : pairFieldsMatchB 188160 facet0 facet751 key0 key859 rowPose859 = true := by decide +kernel
theorem row859_generated : rootPair 859 = some rowPose859 :=
  pairFieldsMatchB_sound (by decide) row859_fields
theorem row859_source : sourceKey 859 ∈ geometry.profile (sourceOwner 859) := by decide +kernel
theorem row859_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 751 key0).FastValid geometry rowPose859 := by decide +kernel
theorem row859_illegal : ¬ geometry.LegalContact rowPose859 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row859_reject_checked)
theorem row859_classified : RowClassified 859 := by
  intro p generated legal
  have he : rowPose859 = p := Option.some.inj (row859_generated.symm.trans generated)
  subst p
  exact (row859_illegal legal).elim

def rowPose860 : Pose 7 := ⟨perm21, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row860_fields : pairFieldsMatchB 188160 facet0 facet752 key0 key860 rowPose860 = true := by decide +kernel
theorem row860_generated : rootPair 860 = some rowPose860 :=
  pairFieldsMatchB_sound (by decide) row860_fields
theorem row860_source : sourceKey 860 ∈ geometry.profile (sourceOwner 860) := by decide +kernel
theorem row860_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 752 key1).FastValid geometry rowPose860 := by decide +kernel
theorem row860_illegal : ¬ geometry.LegalContact rowPose860 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row860_reject_checked)
theorem row860_classified : RowClassified 860 := by
  intro p generated legal
  have he : rowPose860 = p := Option.some.inj (row860_generated.symm.trans generated)
  subst p
  exact (row860_illegal legal).elim

def rowPose861 : Pose 7 := ⟨perm42, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row861_fields : pairFieldsMatchB 188160 facet0 facet753 key0 key861 rowPose861 = true := by decide +kernel
theorem row861_generated : rootPair 861 = some rowPose861 :=
  pairFieldsMatchB_sound (by decide) row861_fields
theorem row861_source : sourceKey 861 ∈ geometry.profile (sourceOwner 861) := by decide +kernel
theorem row861_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 753 key1).FastValid geometry rowPose861 := by decide +kernel
theorem row861_illegal : ¬ geometry.LegalContact rowPose861 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row861_reject_checked)
theorem row861_classified : RowClassified 861 := by
  intro p generated legal
  have he : rowPose861 = p := Option.some.inj (row861_generated.symm.trans generated)
  subst p
  exact (row861_illegal legal).elim

def rowPose862 : Pose 7 := ⟨perm53, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row862_fields : pairFieldsMatchB 188160 facet0 facet754 key0 key862 rowPose862 = true := by decide +kernel
theorem row862_generated : rootPair 862 = some rowPose862 :=
  pairFieldsMatchB_sound (by decide) row862_fields
theorem row862_source : sourceKey 862 ∈ geometry.profile (sourceOwner 862) := by decide +kernel
theorem row862_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 754 key0).FastValid geometry rowPose862 := by decide +kernel
theorem row862_illegal : ¬ geometry.LegalContact rowPose862 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row862_reject_checked)
theorem row862_classified : RowClassified 862 := by
  intro p generated legal
  have he : rowPose862 = p := Option.some.inj (row862_generated.symm.trans generated)
  subst p
  exact (row862_illegal legal).elim

def rowPose863 : Pose 7 := ⟨perm58, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row863_fields : pairFieldsMatchB 188160 facet0 facet754 key0 key863 rowPose863 = true := by decide +kernel
theorem row863_generated : rootPair 863 = some rowPose863 :=
  pairFieldsMatchB_sound (by decide) row863_fields
theorem row863_source : sourceKey 863 ∈ geometry.profile (sourceOwner 863) := by decide +kernel
theorem row863_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 868 key8).FastValid geometry rowPose863 := by decide +kernel
theorem row863_illegal : ¬ geometry.LegalContact rowPose863 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row863_reject_checked)
theorem row863_classified : RowClassified 863 := by
  intro p generated legal
  have he : rowPose863 = p := Option.some.inj (row863_generated.symm.trans generated)
  subst p
  exact (row863_illegal legal).elim

theorem chunk26_classified (i : Fin 32) : RowClassified ⟨832 + i.val, by omega⟩ := by
  fin_cases i
  · exact row832_classified
  · exact row833_classified
  · exact row834_classified
  · exact row835_classified
  · exact row836_classified
  · exact row837_classified
  · exact row838_classified
  · exact row839_classified
  · exact row840_classified
  · exact row841_classified
  · exact row842_classified
  · exact row843_classified
  · exact row844_classified
  · exact row845_classified
  · exact row846_classified
  · exact row847_classified
  · exact row848_classified
  · exact row849_classified
  · exact row850_classified
  · exact row851_classified
  · exact row852_classified
  · exact row853_classified
  · exact row854_classified
  · exact row855_classified
  · exact row856_classified
  · exact row857_classified
  · exact row858_classified
  · exact row859_classified
  · exact row860_classified
  · exact row861_classified
  · exact row862_classified
  · exact row863_classified

theorem chunk26_source (i : Fin 32) : sourceKey ⟨832 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨832 + i.val, by omega⟩) := by
  fin_cases i
  · exact row832_source
  · exact row833_source
  · exact row834_source
  · exact row835_source
  · exact row836_source
  · exact row837_source
  · exact row838_source
  · exact row839_source
  · exact row840_source
  · exact row841_source
  · exact row842_source
  · exact row843_source
  · exact row844_source
  · exact row845_source
  · exact row846_source
  · exact row847_source
  · exact row848_source
  · exact row849_source
  · exact row850_source
  · exact row851_source
  · exact row852_source
  · exact row853_source
  · exact row854_source
  · exact row855_source
  · exact row856_source
  · exact row857_source
  · exact row858_source
  · exact row859_source
  · exact row860_source
  · exact row861_source
  · exact row862_source
  · exact row863_source

#print axioms chunk26_classified
end SparseMonotiles.Contact.RootZeroPilot7
