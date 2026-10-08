module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose896 : Pose 7 := ⟨perm53, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row896_fields : pairFieldsMatchB 188160 facet0 facet783 key0 key896 rowPose896 = true := by decide +kernel
theorem row896_generated : rootPair 896 = some rowPose896 :=
  pairFieldsMatchB_sound (by decide) row896_fields
theorem row896_source : sourceKey 896 ∈ geometry.profile (sourceOwner 896) := by decide +kernel
theorem row896_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 783 key1).FastValid geometry rowPose896 := by decide +kernel
theorem row896_illegal : ¬ geometry.LegalContact rowPose896 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row896_reject_checked)
theorem row896_classified : RowClassified 896 := by
  intro p generated legal
  have he : rowPose896 = p := Option.some.inj (row896_generated.symm.trans generated)
  subst p
  exact (row896_illegal legal).elim

def rowPose897 : Pose 7 := ⟨perm74, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row897_fields : pairFieldsMatchB 188160 facet0 facet784 key0 key897 rowPose897 = true := by decide +kernel
theorem row897_generated : rootPair 897 = some rowPose897 :=
  pairFieldsMatchB_sound (by decide) row897_fields
theorem row897_source : sourceKey 897 ∈ geometry.profile (sourceOwner 897) := by decide +kernel
theorem row897_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 784 key1).FastValid geometry rowPose897 := by decide +kernel
theorem row897_illegal : ¬ geometry.LegalContact rowPose897 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row897_reject_checked)
theorem row897_classified : RowClassified 897 := by
  intro p generated legal
  have he : rowPose897 = p := Option.some.inj (row897_generated.symm.trans generated)
  subst p
  exact (row897_illegal legal).elim

def rowPose898 : Pose 7 := ⟨perm89, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row898_fields : pairFieldsMatchB 188160 facet0 facet785 key0 key898 rowPose898 = true := by decide +kernel
theorem row898_generated : rootPair 898 = some rowPose898 :=
  pairFieldsMatchB_sound (by decide) row898_fields
theorem row898_source : sourceKey 898 ∈ geometry.profile (sourceOwner 898) := by decide +kernel
theorem row898_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 785 key0).FastValid geometry rowPose898 := by decide +kernel
theorem row898_illegal : ¬ geometry.LegalContact rowPose898 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row898_reject_checked)
theorem row898_classified : RowClassified 898 := by
  intro p generated legal
  have he : rowPose898 = p := Option.some.inj (row898_generated.symm.trans generated)
  subst p
  exact (row898_illegal legal).elim

def rowPose899 : Pose 7 := ⟨perm101, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row899_fields : pairFieldsMatchB 188160 facet0 facet786 key0 key899 rowPose899 = true := by decide +kernel
theorem row899_generated : rootPair 899 = some rowPose899 :=
  pairFieldsMatchB_sound (by decide) row899_fields
theorem row899_source : sourceKey 899 ∈ geometry.profile (sourceOwner 899) := by decide +kernel
theorem row899_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 786 key1).FastValid geometry rowPose899 := by decide +kernel
theorem row899_illegal : ¬ geometry.LegalContact rowPose899 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row899_reject_checked)
theorem row899_classified : RowClassified 899 := by
  intro p generated legal
  have he : rowPose899 = p := Option.some.inj (row899_generated.symm.trans generated)
  subst p
  exact (row899_illegal legal).elim

def rowPose900 : Pose 7 := ⟨perm0, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row900_fields : pairFieldsMatchB 188160 facet0 facet787 key0 key900 rowPose900 = true := by decide +kernel
theorem row900_generated : rootPair 900 = some rowPose900 :=
  pairFieldsMatchB_sound (by decide) row900_fields
theorem row900_source : sourceKey 900 ∈ geometry.profile (sourceOwner 900) := by decide +kernel
theorem row900_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 787 key1).FastValid geometry rowPose900 := by decide +kernel
theorem row900_illegal : ¬ geometry.LegalContact rowPose900 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row900_reject_checked)
theorem row900_classified : RowClassified 900 := by
  intro p generated legal
  have he : rowPose900 = p := Option.some.inj (row900_generated.symm.trans generated)
  subst p
  exact (row900_illegal legal).elim

def rowPose901 : Pose 7 := ⟨perm21, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row901_fields : pairFieldsMatchB 188160 facet0 facet788 key0 key901 rowPose901 = true := by decide +kernel
theorem row901_generated : rootPair 901 = some rowPose901 :=
  pairFieldsMatchB_sound (by decide) row901_fields
theorem row901_source : sourceKey 901 ∈ geometry.profile (sourceOwner 901) := by decide +kernel
theorem row901_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 788 key0).FastValid geometry rowPose901 := by decide +kernel
theorem row901_illegal : ¬ geometry.LegalContact rowPose901 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row901_reject_checked)
theorem row901_classified : RowClassified 901 := by
  intro p generated legal
  have he : rowPose901 = p := Option.some.inj (row901_generated.symm.trans generated)
  subst p
  exact (row901_illegal legal).elim

def rowPose902 : Pose 7 := ⟨perm24, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row902_fields : pairFieldsMatchB 188160 facet0 facet788 key0 key902 rowPose902 = true := by decide +kernel
theorem row902_generated : rootPair 902 = some rowPose902 :=
  pairFieldsMatchB_sound (by decide) row902_fields
theorem row902_source : sourceKey 902 ∈ geometry.profile (sourceOwner 902) := by decide +kernel
theorem row902_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 337 key8).FastValid geometry rowPose902 := by decide +kernel
theorem row902_illegal : ¬ geometry.LegalContact rowPose902 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row902_reject_checked)
theorem row902_classified : RowClassified 902 := by
  intro p generated legal
  have he : rowPose902 = p := Option.some.inj (row902_generated.symm.trans generated)
  subst p
  exact (row902_illegal legal).elim

def rowPose903 : Pose 7 := ⟨perm37, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row903_fields : pairFieldsMatchB 188160 facet0 facet789 key0 key903 rowPose903 = true := by decide +kernel
theorem row903_generated : rootPair 903 = some rowPose903 :=
  pairFieldsMatchB_sound (by decide) row903_fields
theorem row903_source : sourceKey 903 ∈ geometry.profile (sourceOwner 903) := by decide +kernel
theorem row903_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 789 key0).FastValid geometry rowPose903 := by decide +kernel
theorem row903_illegal : ¬ geometry.LegalContact rowPose903 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row903_reject_checked)
theorem row903_classified : RowClassified 903 := by
  intro p generated legal
  have he : rowPose903 = p := Option.some.inj (row903_generated.symm.trans generated)
  subst p
  exact (row903_illegal legal).elim

def rowPose904 : Pose 7 := ⟨perm58, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row904_fields : pairFieldsMatchB 188160 facet0 facet790 key0 key904 rowPose904 = true := by decide +kernel
theorem row904_generated : rootPair 904 = some rowPose904 :=
  pairFieldsMatchB_sound (by decide) row904_fields
theorem row904_source : sourceKey 904 ∈ geometry.profile (sourceOwner 904) := by decide +kernel
theorem row904_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 790 key0).FastValid geometry rowPose904 := by decide +kernel
theorem row904_illegal : ¬ geometry.LegalContact rowPose904 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row904_reject_checked)
theorem row904_classified : RowClassified 904 := by
  intro p generated legal
  have he : rowPose904 = p := Option.some.inj (row904_generated.symm.trans generated)
  subst p
  exact (row904_illegal legal).elim

def rowPose905 : Pose 7 := ⟨perm71, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row905_fields : pairFieldsMatchB 188160 facet0 facet791 key0 key905 rowPose905 = true := by decide +kernel
theorem row905_generated : rootPair 905 = some rowPose905 :=
  pairFieldsMatchB_sound (by decide) row905_fields
theorem row905_source : sourceKey 905 ∈ geometry.profile (sourceOwner 905) := by decide +kernel
theorem row905_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 791 key1).FastValid geometry rowPose905 := by decide +kernel
theorem row905_illegal : ¬ geometry.LegalContact rowPose905 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row905_reject_checked)
theorem row905_classified : RowClassified 905 := by
  intro p generated legal
  have he : rowPose905 = p := Option.some.inj (row905_generated.symm.trans generated)
  subst p
  exact (row905_illegal legal).elim

def rowPose906 : Pose 7 := ⟨perm95, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row906_fields : pairFieldsMatchB 188160 facet0 facet792 key0 key906 rowPose906 = true := by decide +kernel
theorem row906_generated : rootPair 906 = some rowPose906 :=
  pairFieldsMatchB_sound (by decide) row906_fields
theorem row906_source : sourceKey 906 ∈ geometry.profile (sourceOwner 906) := by decide +kernel
theorem row906_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 792 key0).FastValid geometry rowPose906 := by decide +kernel
theorem row906_illegal : ¬ geometry.LegalContact rowPose906 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row906_reject_checked)
theorem row906_classified : RowClassified 906 := by
  intro p generated legal
  have he : rowPose906 = p := Option.some.inj (row906_generated.symm.trans generated)
  subst p
  exact (row906_illegal legal).elim

def rowPose907 : Pose 7 := ⟨perm111, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row907_fields : pairFieldsMatchB 188160 facet0 facet793 key0 key907 rowPose907 = true := by decide +kernel
theorem row907_generated : rootPair 907 = some rowPose907 :=
  pairFieldsMatchB_sound (by decide) row907_fields
theorem row907_source : sourceKey 907 ∈ geometry.profile (sourceOwner 907) := by decide +kernel
theorem row907_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 793 key1).FastValid geometry rowPose907 := by decide +kernel
theorem row907_illegal : ¬ geometry.LegalContact rowPose907 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row907_reject_checked)
theorem row907_classified : RowClassified 907 := by
  intro p generated legal
  have he : rowPose907 = p := Option.some.inj (row907_generated.symm.trans generated)
  subst p
  exact (row907_illegal legal).elim

def rowPose908 : Pose 7 := ⟨perm10, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row908_fields : pairFieldsMatchB 188160 facet0 facet794 key0 key908 rowPose908 = true := by decide +kernel
theorem row908_generated : rootPair 908 = some rowPose908 :=
  pairFieldsMatchB_sound (by decide) row908_fields
theorem row908_source : sourceKey 908 ∈ geometry.profile (sourceOwner 908) := by decide +kernel
theorem row908_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 794 key0).FastValid geometry rowPose908 := by decide +kernel
theorem row908_illegal : ¬ geometry.LegalContact rowPose908 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row908_reject_checked)
theorem row908_classified : RowClassified 908 := by
  intro p generated legal
  have he : rowPose908 = p := Option.some.inj (row908_generated.symm.trans generated)
  subst p
  exact (row908_illegal legal).elim

def rowPose909 : Pose 7 := ⟨perm22, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row909_fields : pairFieldsMatchB 188160 facet0 facet795 key0 key909 rowPose909 = true := by decide +kernel
theorem row909_generated : rootPair 909 = some rowPose909 :=
  pairFieldsMatchB_sound (by decide) row909_fields
theorem row909_source : sourceKey 909 ∈ geometry.profile (sourceOwner 909) := by decide +kernel
theorem row909_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 795 key1).FastValid geometry rowPose909 := by decide +kernel
theorem row909_illegal : ¬ geometry.LegalContact rowPose909 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row909_reject_checked)
theorem row909_classified : RowClassified 909 := by
  intro p generated legal
  have he : rowPose909 = p := Option.some.inj (row909_generated.symm.trans generated)
  subst p
  exact (row909_illegal legal).elim

def rowPose910 : Pose 7 := ⟨perm37, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row910_fields : pairFieldsMatchB 188160 facet0 facet796 key0 key910 rowPose910 = true := by decide +kernel
theorem row910_generated : rootPair 910 = some rowPose910 :=
  pairFieldsMatchB_sound (by decide) row910_fields
theorem row910_source : sourceKey 910 ∈ geometry.profile (sourceOwner 910) := by decide +kernel
theorem row910_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 796 key0).FastValid geometry rowPose910 := by decide +kernel
theorem row910_illegal : ¬ geometry.LegalContact rowPose910 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row910_reject_checked)
theorem row910_classified : RowClassified 910 := by
  intro p generated legal
  have he : rowPose910 = p := Option.some.inj (row910_generated.symm.trans generated)
  subst p
  exact (row910_illegal legal).elim

def rowPose911 : Pose 7 := ⟨perm58, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row911_fields : pairFieldsMatchB 188160 facet0 facet797 key0 key911 rowPose911 = true := by decide +kernel
theorem row911_generated : rootPair 911 = some rowPose911 :=
  pairFieldsMatchB_sound (by decide) row911_fields
theorem row911_source : sourceKey 911 ∈ geometry.profile (sourceOwner 911) := by decide +kernel
theorem row911_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 797 key0).FastValid geometry rowPose911 := by decide +kernel
theorem row911_illegal : ¬ geometry.LegalContact rowPose911 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row911_reject_checked)
theorem row911_classified : RowClassified 911 := by
  intro p generated legal
  have he : rowPose911 = p := Option.some.inj (row911_generated.symm.trans generated)
  subst p
  exact (row911_illegal legal).elim

def rowPose912 : Pose 7 := ⟨perm74, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row912_fields : pairFieldsMatchB 188160 facet0 facet798 key0 key912 rowPose912 = true := by decide +kernel
theorem row912_generated : rootPair 912 = some rowPose912 :=
  pairFieldsMatchB_sound (by decide) row912_fields
theorem row912_source : sourceKey 912 ∈ geometry.profile (sourceOwner 912) := by decide +kernel
theorem row912_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 798 key0).FastValid geometry rowPose912 := by decide +kernel
theorem row912_illegal : ¬ geometry.LegalContact rowPose912 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row912_reject_checked)
theorem row912_classified : RowClassified 912 := by
  intro p generated legal
  have he : rowPose912 = p := Option.some.inj (row912_generated.symm.trans generated)
  subst p
  exact (row912_illegal legal).elim

def rowPose913 : Pose 7 := ⟨perm69, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row913_fields : pairFieldsMatchB 188160 facet0 facet798 key0 key913 rowPose913 = true := by decide +kernel
theorem row913_generated : rootPair 913 = some rowPose913 :=
  pairFieldsMatchB_sound (by decide) row913_fields
theorem row913_source : sourceKey 913 ∈ geometry.profile (sourceOwner 913) := by decide +kernel
theorem row913_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 812 key8).FastValid geometry rowPose913 := by decide +kernel
theorem row913_illegal : ¬ geometry.LegalContact rowPose913 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row913_reject_checked)
theorem row913_classified : RowClassified 913 := by
  intro p generated legal
  have he : rowPose913 = p := Option.some.inj (row913_generated.symm.trans generated)
  subst p
  exact (row913_illegal legal).elim

def rowPose914 : Pose 7 := ⟨perm87, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row914_fields : pairFieldsMatchB 188160 facet0 facet799 key0 key914 rowPose914 = true := by decide +kernel
theorem row914_generated : rootPair 914 = some rowPose914 :=
  pairFieldsMatchB_sound (by decide) row914_fields
theorem row914_source : sourceKey 914 ∈ geometry.profile (sourceOwner 914) := by decide +kernel
theorem row914_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 799 key1).FastValid geometry rowPose914 := by decide +kernel
theorem row914_illegal : ¬ geometry.LegalContact rowPose914 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row914_reject_checked)
theorem row914_classified : RowClassified 914 := by
  intro p generated legal
  have he : rowPose914 = p := Option.some.inj (row914_generated.symm.trans generated)
  subst p
  exact (row914_illegal legal).elim

def rowPose915 : Pose 7 := ⟨perm96, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row915_fields : pairFieldsMatchB 188160 facet0 facet800 key0 key915 rowPose915 = true := by decide +kernel
theorem row915_generated : rootPair 915 = some rowPose915 :=
  pairFieldsMatchB_sound (by decide) row915_fields
theorem row915_source : sourceKey 915 ∈ geometry.profile (sourceOwner 915) := by decide +kernel
theorem row915_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 800 key1).FastValid geometry rowPose915 := by decide +kernel
theorem row915_illegal : ¬ geometry.LegalContact rowPose915 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row915_reject_checked)
theorem row915_classified : RowClassified 915 := by
  intro p generated legal
  have he : rowPose915 = p := Option.some.inj (row915_generated.symm.trans generated)
  subst p
  exact (row915_illegal legal).elim

def rowPose916 : Pose 7 := ⟨perm15, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row916_fields : pairFieldsMatchB 188160 facet0 facet801 key0 key916 rowPose916 = true := by decide +kernel
theorem row916_generated : rootPair 916 = some rowPose916 :=
  pairFieldsMatchB_sound (by decide) row916_fields
theorem row916_source : sourceKey 916 ∈ geometry.profile (sourceOwner 916) := by decide +kernel
theorem row916_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 801 key0).FastValid geometry rowPose916 := by decide +kernel
theorem row916_illegal : ¬ geometry.LegalContact rowPose916 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row916_reject_checked)
theorem row916_classified : RowClassified 916 := by
  intro p generated legal
  have he : rowPose916 = p := Option.some.inj (row916_generated.symm.trans generated)
  subst p
  exact (row916_illegal legal).elim

def rowPose917 : Pose 7 := ⟨perm24, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row917_fields : pairFieldsMatchB 188160 facet0 facet802 key0 key917 rowPose917 = true := by decide +kernel
theorem row917_generated : rootPair 917 = some rowPose917 :=
  pairFieldsMatchB_sound (by decide) row917_fields
theorem row917_source : sourceKey 917 ∈ geometry.profile (sourceOwner 917) := by decide +kernel
theorem row917_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 802 key0).FastValid geometry rowPose917 := by decide +kernel
theorem row917_illegal : ¬ geometry.LegalContact rowPose917 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row917_reject_checked)
theorem row917_classified : RowClassified 917 := by
  intro p generated legal
  have he : rowPose917 = p := Option.some.inj (row917_generated.symm.trans generated)
  subst p
  exact (row917_illegal legal).elim

def rowPose918 : Pose 7 := ⟨perm37, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row918_fields : pairFieldsMatchB 188160 facet0 facet803 key0 key918 rowPose918 = true := by decide +kernel
theorem row918_generated : rootPair 918 = some rowPose918 :=
  pairFieldsMatchB_sound (by decide) row918_fields
theorem row918_source : sourceKey 918 ∈ geometry.profile (sourceOwner 918) := by decide +kernel
theorem row918_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 860 key8).FastValid geometry rowPose918 := by decide +kernel
theorem row918_illegal : ¬ geometry.LegalContact rowPose918 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row918_reject_checked)
theorem row918_classified : RowClassified 918 := by
  intro p generated legal
  have he : rowPose918 = p := Option.some.inj (row918_generated.symm.trans generated)
  subst p
  exact (row918_illegal legal).elim

def rowPose919 : Pose 7 := ⟨perm42, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row919_fields : pairFieldsMatchB 188160 facet0 facet803 key0 key919 rowPose919 = true := by decide +kernel
theorem row919_generated : rootPair 919 = some rowPose919 :=
  pairFieldsMatchB_sound (by decide) row919_fields
theorem row919_source : sourceKey 919 ∈ geometry.profile (sourceOwner 919) := by decide +kernel
theorem row919_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 803 key0).FastValid geometry rowPose919 := by decide +kernel
theorem row919_illegal : ¬ geometry.LegalContact rowPose919 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row919_reject_checked)
theorem row919_classified : RowClassified 919 := by
  intro p generated legal
  have he : rowPose919 = p := Option.some.inj (row919_generated.symm.trans generated)
  subst p
  exact (row919_illegal legal).elim

def rowPose920 : Pose 7 := ⟨perm53, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row920_fields : pairFieldsMatchB 188160 facet0 facet804 key0 key920 rowPose920 = true := by decide +kernel
theorem row920_generated : rootPair 920 = some rowPose920 :=
  pairFieldsMatchB_sound (by decide) row920_fields
theorem row920_source : sourceKey 920 ∈ geometry.profile (sourceOwner 920) := by decide +kernel
theorem row920_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 804 key1).FastValid geometry rowPose920 := by decide +kernel
theorem row920_illegal : ¬ geometry.LegalContact rowPose920 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row920_reject_checked)
theorem row920_classified : RowClassified 920 := by
  intro p generated legal
  have he : rowPose920 = p := Option.some.inj (row920_generated.symm.trans generated)
  subst p
  exact (row920_illegal legal).elim

def rowPose921 : Pose 7 := ⟨perm74, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row921_fields : pairFieldsMatchB 188160 facet0 facet805 key0 key921 rowPose921 = true := by decide +kernel
theorem row921_generated : rootPair 921 = some rowPose921 :=
  pairFieldsMatchB_sound (by decide) row921_fields
theorem row921_source : sourceKey 921 ∈ geometry.profile (sourceOwner 921) := by decide +kernel
theorem row921_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 805 key1).FastValid geometry rowPose921 := by decide +kernel
theorem row921_illegal : ¬ geometry.LegalContact rowPose921 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row921_reject_checked)
theorem row921_classified : RowClassified 921 := by
  intro p generated legal
  have he : rowPose921 = p := Option.some.inj (row921_generated.symm.trans generated)
  subst p
  exact (row921_illegal legal).elim

def rowPose922 : Pose 7 := ⟨perm89, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row922_fields : pairFieldsMatchB 188160 facet0 facet806 key0 key922 rowPose922 = true := by decide +kernel
theorem row922_generated : rootPair 922 = some rowPose922 :=
  pairFieldsMatchB_sound (by decide) row922_fields
theorem row922_source : sourceKey 922 ∈ geometry.profile (sourceOwner 922) := by decide +kernel
theorem row922_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 806 key0).FastValid geometry rowPose922 := by decide +kernel
theorem row922_illegal : ¬ geometry.LegalContact rowPose922 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row922_reject_checked)
theorem row922_classified : RowClassified 922 := by
  intro p generated legal
  have he : rowPose922 = p := Option.some.inj (row922_generated.symm.trans generated)
  subst p
  exact (row922_illegal legal).elim

def rowPose923 : Pose 7 := ⟨perm101, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row923_fields : pairFieldsMatchB 188160 facet0 facet807 key0 key923 rowPose923 = true := by decide +kernel
theorem row923_generated : rootPair 923 = some rowPose923 :=
  pairFieldsMatchB_sound (by decide) row923_fields
theorem row923_source : sourceKey 923 ∈ geometry.profile (sourceOwner 923) := by decide +kernel
theorem row923_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 807 key1).FastValid geometry rowPose923 := by decide +kernel
theorem row923_illegal : ¬ geometry.LegalContact rowPose923 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row923_reject_checked)
theorem row923_classified : RowClassified 923 := by
  intro p generated legal
  have he : rowPose923 = p := Option.some.inj (row923_generated.symm.trans generated)
  subst p
  exact (row923_illegal legal).elim

def rowPose924 : Pose 7 := ⟨perm0, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row924_fields : pairFieldsMatchB 188160 facet0 facet808 key0 key924 rowPose924 = true := by decide +kernel
theorem row924_generated : rootPair 924 = some rowPose924 :=
  pairFieldsMatchB_sound (by decide) row924_fields
theorem row924_source : sourceKey 924 ∈ geometry.profile (sourceOwner 924) := by decide +kernel
theorem row924_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 801 key8).FastValid geometry rowPose924 := by decide +kernel
theorem row924_illegal : ¬ geometry.LegalContact rowPose924 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row924_reject_checked)
theorem row924_classified : RowClassified 924 := by
  intro p generated legal
  have he : rowPose924 = p := Option.some.inj (row924_generated.symm.trans generated)
  subst p
  exact (row924_illegal legal).elim

def rowPose925 : Pose 7 := ⟨perm15, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row925_fields : pairFieldsMatchB 188160 facet0 facet808 key0 key925 rowPose925 = true := by decide +kernel
theorem row925_generated : rootPair 925 = some rowPose925 :=
  pairFieldsMatchB_sound (by decide) row925_fields
theorem row925_source : sourceKey 925 ∈ geometry.profile (sourceOwner 925) := by decide +kernel
theorem row925_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 808 key0).FastValid geometry rowPose925 := by decide +kernel
theorem row925_illegal : ¬ geometry.LegalContact rowPose925 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row925_reject_checked)
theorem row925_classified : RowClassified 925 := by
  intro p generated legal
  have he : rowPose925 = p := Option.some.inj (row925_generated.symm.trans generated)
  subst p
  exact (row925_illegal legal).elim

def rowPose926 : Pose 7 := ⟨perm21, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row926_fields : pairFieldsMatchB 188160 facet0 facet809 key0 key926 rowPose926 = true := by decide +kernel
theorem row926_generated : rootPair 926 = some rowPose926 :=
  pairFieldsMatchB_sound (by decide) row926_fields
theorem row926_source : sourceKey 926 ∈ geometry.profile (sourceOwner 926) := by decide +kernel
theorem row926_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 809 key0).FastValid geometry rowPose926 := by decide +kernel
theorem row926_illegal : ¬ geometry.LegalContact rowPose926 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row926_reject_checked)
theorem row926_classified : RowClassified 926 := by
  intro p generated legal
  have he : rowPose926 = p := Option.some.inj (row926_generated.symm.trans generated)
  subst p
  exact (row926_illegal legal).elim

def rowPose927 : Pose 7 := ⟨perm42, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row927_fields : pairFieldsMatchB 188160 facet0 facet810 key0 key927 rowPose927 = true := by decide +kernel
theorem row927_generated : rootPair 927 = some rowPose927 :=
  pairFieldsMatchB_sound (by decide) row927_fields
theorem row927_source : sourceKey 927 ∈ geometry.profile (sourceOwner 927) := by decide +kernel
theorem row927_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 810 key0).FastValid geometry rowPose927 := by decide +kernel
theorem row927_illegal : ¬ geometry.LegalContact rowPose927 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row927_reject_checked)
theorem row927_classified : RowClassified 927 := by
  intro p generated legal
  have he : rowPose927 = p := Option.some.inj (row927_generated.symm.trans generated)
  subst p
  exact (row927_illegal legal).elim

theorem chunk28_classified (i : Fin 32) : RowClassified ⟨896 + i.val, by omega⟩ := by
  fin_cases i
  · exact row896_classified
  · exact row897_classified
  · exact row898_classified
  · exact row899_classified
  · exact row900_classified
  · exact row901_classified
  · exact row902_classified
  · exact row903_classified
  · exact row904_classified
  · exact row905_classified
  · exact row906_classified
  · exact row907_classified
  · exact row908_classified
  · exact row909_classified
  · exact row910_classified
  · exact row911_classified
  · exact row912_classified
  · exact row913_classified
  · exact row914_classified
  · exact row915_classified
  · exact row916_classified
  · exact row917_classified
  · exact row918_classified
  · exact row919_classified
  · exact row920_classified
  · exact row921_classified
  · exact row922_classified
  · exact row923_classified
  · exact row924_classified
  · exact row925_classified
  · exact row926_classified
  · exact row927_classified

theorem chunk28_source (i : Fin 32) : sourceKey ⟨896 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨896 + i.val, by omega⟩) := by
  fin_cases i
  · exact row896_source
  · exact row897_source
  · exact row898_source
  · exact row899_source
  · exact row900_source
  · exact row901_source
  · exact row902_source
  · exact row903_source
  · exact row904_source
  · exact row905_source
  · exact row906_source
  · exact row907_source
  · exact row908_source
  · exact row909_source
  · exact row910_source
  · exact row911_source
  · exact row912_source
  · exact row913_source
  · exact row914_source
  · exact row915_source
  · exact row916_source
  · exact row917_source
  · exact row918_source
  · exact row919_source
  · exact row920_source
  · exact row921_source
  · exact row922_source
  · exact row923_source
  · exact row924_source
  · exact row925_source
  · exact row926_source
  · exact row927_source

#print axioms chunk28_classified
end SparseMonotiles.Contact.RootZeroPilot7
