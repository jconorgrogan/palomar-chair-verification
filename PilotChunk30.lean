module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose960 : Pose 7 := ⟨perm58, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row960_fields : pairFieldsMatchB 188160 facet0 facet839 key0 key960 rowPose960 = true := by decide +kernel
theorem row960_generated : rootPair 960 = some rowPose960 :=
  pairFieldsMatchB_sound (by decide) row960_fields
theorem row960_source : sourceKey 960 ∈ geometry.profile (sourceOwner 960) := by decide +kernel
theorem row960_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 839 key0).FastValid geometry rowPose960 := by decide +kernel
theorem row960_illegal : ¬ geometry.LegalContact rowPose960 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row960_reject_checked)
theorem row960_classified : RowClassified 960 := by
  intro p generated legal
  have he : rowPose960 = p := Option.some.inj (row960_generated.symm.trans generated)
  subst p
  exact (row960_illegal legal).elim

def rowPose961 : Pose 7 := ⟨perm55, ![false, true, false, false, true, false, false], ![-1, 2, -1, -1, 2, -1, -1]⟩
theorem row961_fields : pairFieldsMatchB 188160 facet0 facet840 key0 key961 rowPose961 = true := by decide +kernel
theorem row961_generated : rootPair 961 = some rowPose961 :=
  pairFieldsMatchB_sound (by decide) row961_fields
theorem row961_source : sourceKey 961 ∈ geometry.profile (sourceOwner 961) := by decide +kernel
theorem row961_reject_checked : (show IndexedRejection 7 896 from .overlap ![0, 0, 0, 0, 1, 0, 0]).FastValid geometry rowPose961 := by decide +kernel
theorem row961_illegal : ¬ geometry.LegalContact rowPose961 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row961_reject_checked)
theorem row961_classified : RowClassified 961 := by
  intro p generated legal
  have he : rowPose961 = p := Option.some.inj (row961_generated.symm.trans generated)
  subst p
  exact (row961_illegal legal).elim

def rowPose962 : Pose 7 := ⟨perm69, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row962_fields : pairFieldsMatchB 188160 facet0 facet841 key0 key962 rowPose962 = true := by decide +kernel
theorem row962_generated : rootPair 962 = some rowPose962 :=
  pairFieldsMatchB_sound (by decide) row962_fields
theorem row962_source : sourceKey 962 ∈ geometry.profile (sourceOwner 962) := by decide +kernel
theorem row962_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 841 key1).FastValid geometry rowPose962 := by decide +kernel
theorem row962_illegal : ¬ geometry.LegalContact rowPose962 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row962_reject_checked)
theorem row962_classified : RowClassified 962 := by
  intro p generated legal
  have he : rowPose962 = p := Option.some.inj (row962_generated.symm.trans generated)
  subst p
  exact (row962_illegal legal).elim

def rowPose963 : Pose 7 := ⟨perm90, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row963_fields : pairFieldsMatchB 188160 facet0 facet842 key0 key963 rowPose963 = true := by decide +kernel
theorem row963_generated : rootPair 963 = some rowPose963 :=
  pairFieldsMatchB_sound (by decide) row963_fields
theorem row963_source : sourceKey 963 ∈ geometry.profile (sourceOwner 963) := by decide +kernel
theorem row963_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 842 key1).FastValid geometry rowPose963 := by decide +kernel
theorem row963_illegal : ¬ geometry.LegalContact rowPose963 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row963_reject_checked)
theorem row963_classified : RowClassified 963 := by
  intro p generated legal
  have he : rowPose963 = p := Option.some.inj (row963_generated.symm.trans generated)
  subst p
  exact (row963_illegal legal).elim

def rowPose964 : Pose 7 := ⟨perm106, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row964_fields : pairFieldsMatchB 188160 facet0 facet843 key0 key964 rowPose964 = true := by decide +kernel
theorem row964_generated : rootPair 964 = some rowPose964 :=
  pairFieldsMatchB_sound (by decide) row964_fields
theorem row964_source : sourceKey 964 ∈ geometry.profile (sourceOwner 964) := by decide +kernel
theorem row964_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 843 key0).FastValid geometry rowPose964 := by decide +kernel
theorem row964_illegal : ¬ geometry.LegalContact rowPose964 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row964_reject_checked)
theorem row964_classified : RowClassified 964 := by
  intro p generated legal
  have he : rowPose964 = p := Option.some.inj (row964_generated.symm.trans generated)
  subst p
  exact (row964_illegal legal).elim

def rowPose965 : Pose 7 := ⟨perm0, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row965_fields : pairFieldsMatchB 188160 facet0 facet844 key0 key965 rowPose965 = true := by decide +kernel
theorem row965_generated : rootPair 965 = some rowPose965 :=
  pairFieldsMatchB_sound (by decide) row965_fields
theorem row965_source : sourceKey 965 ∈ geometry.profile (sourceOwner 965) := by decide +kernel
theorem row965_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 844 key1).FastValid geometry rowPose965 := by decide +kernel
theorem row965_illegal : ¬ geometry.LegalContact rowPose965 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row965_reject_checked)
theorem row965_classified : RowClassified 965 := by
  intro p generated legal
  have he : rowPose965 = p := Option.some.inj (row965_generated.symm.trans generated)
  subst p
  exact (row965_illegal legal).elim

def rowPose966 : Pose 7 := ⟨perm16, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row966_fields : pairFieldsMatchB 188160 facet0 facet845 key0 key966 rowPose966 = true := by decide +kernel
theorem row966_generated : rootPair 966 = some rowPose966 :=
  pairFieldsMatchB_sound (by decide) row966_fields
theorem row966_source : sourceKey 966 ∈ geometry.profile (sourceOwner 966) := by decide +kernel
theorem row966_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 845 key0).FastValid geometry rowPose966 := by decide +kernel
theorem row966_illegal : ¬ geometry.LegalContact rowPose966 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row966_reject_checked)
theorem row966_classified : RowClassified 966 := by
  intro p generated legal
  have he : rowPose966 = p := Option.some.inj (row966_generated.symm.trans generated)
  subst p
  exact (row966_illegal legal).elim

def rowPose967 : Pose 7 := ⟨perm40, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row967_fields : pairFieldsMatchB 188160 facet0 facet846 key0 key967 rowPose967 = true := by decide +kernel
theorem row967_generated : rootPair 967 = some rowPose967 :=
  pairFieldsMatchB_sound (by decide) row967_fields
theorem row967_source : sourceKey 967 ∈ geometry.profile (sourceOwner 967) := by decide +kernel
theorem row967_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 846 key1).FastValid geometry rowPose967 := by decide +kernel
theorem row967_illegal : ¬ geometry.LegalContact rowPose967 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row967_reject_checked)
theorem row967_classified : RowClassified 967 := by
  intro p generated legal
  have he : rowPose967 = p := Option.some.inj (row967_generated.symm.trans generated)
  subst p
  exact (row967_illegal legal).elim

def rowPose968 : Pose 7 := ⟨perm53, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row968_fields : pairFieldsMatchB 188160 facet0 facet847 key0 key968 rowPose968 = true := by decide +kernel
theorem row968_generated : rootPair 968 = some rowPose968 :=
  pairFieldsMatchB_sound (by decide) row968_fields
theorem row968_source : sourceKey 968 ∈ geometry.profile (sourceOwner 968) := by decide +kernel
theorem row968_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 847 key0).FastValid geometry rowPose968 := by decide +kernel
theorem row968_illegal : ¬ geometry.LegalContact rowPose968 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row968_reject_checked)
theorem row968_classified : RowClassified 968 := by
  intro p generated legal
  have he : rowPose968 = p := Option.some.inj (row968_generated.symm.trans generated)
  subst p
  exact (row968_illegal legal).elim

def rowPose969 : Pose 7 := ⟨perm74, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row969_fields : pairFieldsMatchB 188160 facet0 facet848 key0 key969 rowPose969 = true := by decide +kernel
theorem row969_generated : rootPair 969 = some rowPose969 :=
  pairFieldsMatchB_sound (by decide) row969_fields
theorem row969_source : sourceKey 969 ∈ geometry.profile (sourceOwner 969) := by decide +kernel
theorem row969_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 848 key0).FastValid geometry rowPose969 := by decide +kernel
theorem row969_illegal : ¬ geometry.LegalContact rowPose969 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row969_reject_checked)
theorem row969_classified : RowClassified 969 := by
  intro p generated legal
  have he : rowPose969 = p := Option.some.inj (row969_generated.symm.trans generated)
  subst p
  exact (row969_illegal legal).elim

def rowPose970 : Pose 7 := ⟨perm90, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row970_fields : pairFieldsMatchB 188160 facet0 facet849 key0 key970 rowPose970 = true := by decide +kernel
theorem row970_generated : rootPair 970 = some rowPose970 :=
  pairFieldsMatchB_sound (by decide) row970_fields
theorem row970_source : sourceKey 970 ∈ geometry.profile (sourceOwner 970) := by decide +kernel
theorem row970_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 849 key0).FastValid geometry rowPose970 := by decide +kernel
theorem row970_illegal : ¬ geometry.LegalContact rowPose970 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row970_reject_checked)
theorem row970_classified : RowClassified 970 := by
  intro p generated legal
  have he : rowPose970 = p := Option.some.inj (row970_generated.symm.trans generated)
  subst p
  exact (row970_illegal legal).elim

def rowPose971 : Pose 7 := ⟨perm87, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row971_fields : pairFieldsMatchB 188160 facet0 facet849 key0 key971 rowPose971 = true := by decide +kernel
theorem row971_generated : rootPair 971 = some rowPose971 :=
  pairFieldsMatchB_sound (by decide) row971_fields
theorem row971_source : sourceKey 971 ∈ geometry.profile (sourceOwner 971) := by decide +kernel
theorem row971_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 856 key8).FastValid geometry rowPose971 := by decide +kernel
theorem row971_illegal : ¬ geometry.LegalContact rowPose971 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row971_reject_checked)
theorem row971_classified : RowClassified 971 := by
  intro p generated legal
  have he : rowPose971 = p := Option.some.inj (row971_generated.symm.trans generated)
  subst p
  exact (row971_illegal legal).elim

def rowPose972 : Pose 7 := ⟨perm111, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row972_fields : pairFieldsMatchB 188160 facet0 facet850 key0 key972 rowPose972 = true := by decide +kernel
theorem row972_generated : rootPair 972 = some rowPose972 :=
  pairFieldsMatchB_sound (by decide) row972_fields
theorem row972_source : sourceKey 972 ∈ geometry.profile (sourceOwner 972) := by decide +kernel
theorem row972_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 850 key1).FastValid geometry rowPose972 := by decide +kernel
theorem row972_illegal : ¬ geometry.LegalContact rowPose972 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row972_reject_checked)
theorem row972_classified : RowClassified 972 := by
  intro p generated legal
  have he : rowPose972 = p := Option.some.inj (row972_generated.symm.trans generated)
  subst p
  exact (row972_illegal legal).elim

def rowPose973 : Pose 7 := ⟨perm0, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row973_fields : pairFieldsMatchB 188160 facet0 facet851 key0 key973 rowPose973 = true := by decide +kernel
theorem row973_generated : rootPair 973 = some rowPose973 :=
  pairFieldsMatchB_sound (by decide) row973_fields
theorem row973_source : sourceKey 973 ∈ geometry.profile (sourceOwner 973) := by decide +kernel
theorem row973_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 851 key1).FastValid geometry rowPose973 := by decide +kernel
theorem row973_illegal : ¬ geometry.LegalContact rowPose973 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row973_reject_checked)
theorem row973_classified : RowClassified 973 := by
  intro p generated legal
  have he : rowPose973 = p := Option.some.inj (row973_generated.symm.trans generated)
  subst p
  exact (row973_illegal legal).elim

def rowPose974 : Pose 7 := ⟨perm21, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row974_fields : pairFieldsMatchB 188160 facet0 facet852 key0 key974 rowPose974 = true := by decide +kernel
theorem row974_generated : rootPair 974 = some rowPose974 :=
  pairFieldsMatchB_sound (by decide) row974_fields
theorem row974_source : sourceKey 974 ∈ geometry.profile (sourceOwner 974) := by decide +kernel
theorem row974_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 852 key0).FastValid geometry rowPose974 := by decide +kernel
theorem row974_illegal : ¬ geometry.LegalContact rowPose974 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row974_reject_checked)
theorem row974_classified : RowClassified 974 := by
  intro p generated legal
  have he : rowPose974 = p := Option.some.inj (row974_generated.symm.trans generated)
  subst p
  exact (row974_illegal legal).elim

def rowPose975 : Pose 7 := ⟨perm24, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row975_fields : pairFieldsMatchB 188160 facet0 facet852 key0 key975 rowPose975 = true := by decide +kernel
theorem row975_generated : rootPair 975 = some rowPose975 :=
  pairFieldsMatchB_sound (by decide) row975_fields
theorem row975_source : sourceKey 975 ∈ geometry.profile (sourceOwner 975) := by decide +kernel
theorem row975_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 400 key8).FastValid geometry rowPose975 := by decide +kernel
theorem row975_illegal : ¬ geometry.LegalContact rowPose975 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row975_reject_checked)
theorem row975_classified : RowClassified 975 := by
  intro p generated legal
  have he : rowPose975 = p := Option.some.inj (row975_generated.symm.trans generated)
  subst p
  exact (row975_illegal legal).elim

def rowPose976 : Pose 7 := ⟨perm37, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row976_fields : pairFieldsMatchB 188160 facet0 facet853 key0 key976 rowPose976 = true := by decide +kernel
theorem row976_generated : rootPair 976 = some rowPose976 :=
  pairFieldsMatchB_sound (by decide) row976_fields
theorem row976_source : sourceKey 976 ∈ geometry.profile (sourceOwner 976) := by decide +kernel
theorem row976_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 853 key0).FastValid geometry rowPose976 := by decide +kernel
theorem row976_illegal : ¬ geometry.LegalContact rowPose976 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row976_reject_checked)
theorem row976_classified : RowClassified 976 := by
  intro p generated legal
  have he : rowPose976 = p := Option.some.inj (row976_generated.symm.trans generated)
  subst p
  exact (row976_illegal legal).elim

def rowPose977 : Pose 7 := ⟨perm58, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row977_fields : pairFieldsMatchB 188160 facet0 facet854 key0 key977 rowPose977 = true := by decide +kernel
theorem row977_generated : rootPair 977 = some rowPose977 :=
  pairFieldsMatchB_sound (by decide) row977_fields
theorem row977_source : sourceKey 977 ∈ geometry.profile (sourceOwner 977) := by decide +kernel
theorem row977_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 854 key0).FastValid geometry rowPose977 := by decide +kernel
theorem row977_illegal : ¬ geometry.LegalContact rowPose977 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row977_reject_checked)
theorem row977_classified : RowClassified 977 := by
  intro p generated legal
  have he : rowPose977 = p := Option.some.inj (row977_generated.symm.trans generated)
  subst p
  exact (row977_illegal legal).elim

def rowPose978 : Pose 7 := ⟨perm71, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row978_fields : pairFieldsMatchB 188160 facet0 facet855 key0 key978 rowPose978 = true := by decide +kernel
theorem row978_generated : rootPair 978 = some rowPose978 :=
  pairFieldsMatchB_sound (by decide) row978_fields
theorem row978_source : sourceKey 978 ∈ geometry.profile (sourceOwner 978) := by decide +kernel
theorem row978_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 855 key1).FastValid geometry rowPose978 := by decide +kernel
theorem row978_illegal : ¬ geometry.LegalContact rowPose978 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row978_reject_checked)
theorem row978_classified : RowClassified 978 := by
  intro p generated legal
  have he : rowPose978 = p := Option.some.inj (row978_generated.symm.trans generated)
  subst p
  exact (row978_illegal legal).elim

def rowPose979 : Pose 7 := ⟨perm95, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row979_fields : pairFieldsMatchB 188160 facet0 facet856 key0 key979 rowPose979 = true := by decide +kernel
theorem row979_generated : rootPair 979 = some rowPose979 :=
  pairFieldsMatchB_sound (by decide) row979_fields
theorem row979_source : sourceKey 979 ∈ geometry.profile (sourceOwner 979) := by decide +kernel
theorem row979_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 856 key0).FastValid geometry rowPose979 := by decide +kernel
theorem row979_illegal : ¬ geometry.LegalContact rowPose979 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row979_reject_checked)
theorem row979_classified : RowClassified 979 := by
  intro p generated legal
  have he : rowPose979 = p := Option.some.inj (row979_generated.symm.trans generated)
  subst p
  exact (row979_illegal legal).elim

def rowPose980 : Pose 7 := ⟨perm111, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row980_fields : pairFieldsMatchB 188160 facet0 facet857 key0 key980 rowPose980 = true := by decide +kernel
theorem row980_generated : rootPair 980 = some rowPose980 :=
  pairFieldsMatchB_sound (by decide) row980_fields
theorem row980_source : sourceKey 980 ∈ geometry.profile (sourceOwner 980) := by decide +kernel
theorem row980_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 857 key1).FastValid geometry rowPose980 := by decide +kernel
theorem row980_illegal : ¬ geometry.LegalContact rowPose980 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row980_reject_checked)
theorem row980_classified : RowClassified 980 := by
  intro p generated legal
  have he : rowPose980 = p := Option.some.inj (row980_generated.symm.trans generated)
  subst p
  exact (row980_illegal legal).elim

def rowPose981 : Pose 7 := ⟨perm0, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row981_fields : pairFieldsMatchB 188160 facet0 facet858 key0 key981 rowPose981 = true := by decide +kernel
theorem row981_generated : rootPair 981 = some rowPose981 :=
  pairFieldsMatchB_sound (by decide) row981_fields
theorem row981_source : sourceKey 981 ∈ geometry.profile (sourceOwner 981) := by decide +kernel
theorem row981_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 858 key0).FastValid geometry rowPose981 := by decide +kernel
theorem row981_illegal : ¬ geometry.LegalContact rowPose981 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row981_reject_checked)
theorem row981_classified : RowClassified 981 := by
  intro p generated legal
  have he : rowPose981 = p := Option.some.inj (row981_generated.symm.trans generated)
  subst p
  exact (row981_illegal legal).elim

def rowPose982 : Pose 7 := ⟨perm16, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row982_fields : pairFieldsMatchB 188160 facet0 facet859 key0 key982 rowPose982 = true := by decide +kernel
theorem row982_generated : rootPair 982 = some rowPose982 :=
  pairFieldsMatchB_sound (by decide) row982_fields
theorem row982_source : sourceKey 982 ∈ geometry.profile (sourceOwner 982) := by decide +kernel
theorem row982_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 859 key1).FastValid geometry rowPose982 := by decide +kernel
theorem row982_illegal : ¬ geometry.LegalContact rowPose982 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row982_reject_checked)
theorem row982_classified : RowClassified 982 := by
  intro p generated legal
  have he : rowPose982 = p := Option.some.inj (row982_generated.symm.trans generated)
  subst p
  exact (row982_illegal legal).elim

def rowPose983 : Pose 7 := ⟨perm40, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row983_fields : pairFieldsMatchB 188160 facet0 facet860 key0 key983 rowPose983 = true := by decide +kernel
theorem row983_generated : rootPair 983 = some rowPose983 :=
  pairFieldsMatchB_sound (by decide) row983_fields
theorem row983_source : sourceKey 983 ∈ geometry.profile (sourceOwner 983) := by decide +kernel
theorem row983_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 860 key0).FastValid geometry rowPose983 := by decide +kernel
theorem row983_illegal : ¬ geometry.LegalContact rowPose983 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row983_reject_checked)
theorem row983_classified : RowClassified 983 := by
  intro p generated legal
  have he : rowPose983 = p := Option.some.inj (row983_generated.symm.trans generated)
  subst p
  exact (row983_illegal legal).elim

def rowPose984 : Pose 7 := ⟨perm53, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row984_fields : pairFieldsMatchB 188160 facet0 facet861 key0 key984 rowPose984 = true := by decide +kernel
theorem row984_generated : rootPair 984 = some rowPose984 :=
  pairFieldsMatchB_sound (by decide) row984_fields
theorem row984_source : sourceKey 984 ∈ geometry.profile (sourceOwner 984) := by decide +kernel
theorem row984_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 861 key1).FastValid geometry rowPose984 := by decide +kernel
theorem row984_illegal : ¬ geometry.LegalContact rowPose984 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row984_reject_checked)
theorem row984_classified : RowClassified 984 := by
  intro p generated legal
  have he : rowPose984 = p := Option.some.inj (row984_generated.symm.trans generated)
  subst p
  exact (row984_illegal legal).elim

def rowPose985 : Pose 7 := ⟨perm74, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row985_fields : pairFieldsMatchB 188160 facet0 facet862 key0 key985 rowPose985 = true := by decide +kernel
theorem row985_generated : rootPair 985 = some rowPose985 :=
  pairFieldsMatchB_sound (by decide) row985_fields
theorem row985_source : sourceKey 985 ∈ geometry.profile (sourceOwner 985) := by decide +kernel
theorem row985_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 862 key1).FastValid geometry rowPose985 := by decide +kernel
theorem row985_illegal : ¬ geometry.LegalContact rowPose985 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row985_reject_checked)
theorem row985_classified : RowClassified 985 := by
  intro p generated legal
  have he : rowPose985 = p := Option.some.inj (row985_generated.symm.trans generated)
  subst p
  exact (row985_illegal legal).elim

def rowPose986 : Pose 7 := ⟨perm90, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row986_fields : pairFieldsMatchB 188160 facet0 facet863 key0 key986 rowPose986 = true := by decide +kernel
theorem row986_generated : rootPair 986 = some rowPose986 :=
  pairFieldsMatchB_sound (by decide) row986_fields
theorem row986_source : sourceKey 986 ∈ geometry.profile (sourceOwner 986) := by decide +kernel
theorem row986_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 893 key8).FastValid geometry rowPose986 := by decide +kernel
theorem row986_illegal : ¬ geometry.LegalContact rowPose986 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row986_reject_checked)
theorem row986_classified : RowClassified 986 := by
  intro p generated legal
  have he : rowPose986 = p := Option.some.inj (row986_generated.symm.trans generated)
  subst p
  exact (row986_illegal legal).elim

def rowPose987 : Pose 7 := ⟨perm87, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row987_fields : pairFieldsMatchB 188160 facet0 facet863 key0 key987 rowPose987 = true := by decide +kernel
theorem row987_generated : rootPair 987 = some rowPose987 :=
  pairFieldsMatchB_sound (by decide) row987_fields
theorem row987_source : sourceKey 987 ∈ geometry.profile (sourceOwner 987) := by decide +kernel
theorem row987_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 863 key0).FastValid geometry rowPose987 := by decide +kernel
theorem row987_illegal : ¬ geometry.LegalContact rowPose987 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row987_reject_checked)
theorem row987_classified : RowClassified 987 := by
  intro p generated legal
  have he : rowPose987 = p := Option.some.inj (row987_generated.symm.trans generated)
  subst p
  exact (row987_illegal legal).elim

def rowPose988 : Pose 7 := ⟨perm111, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row988_fields : pairFieldsMatchB 188160 facet0 facet864 key0 key988 rowPose988 = true := by decide +kernel
theorem row988_generated : rootPair 988 = some rowPose988 :=
  pairFieldsMatchB_sound (by decide) row988_fields
theorem row988_source : sourceKey 988 ∈ geometry.profile (sourceOwner 988) := by decide +kernel
theorem row988_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 864 key0).FastValid geometry rowPose988 := by decide +kernel
theorem row988_illegal : ¬ geometry.LegalContact rowPose988 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row988_reject_checked)
theorem row988_classified : RowClassified 988 := by
  intro p generated legal
  have he : rowPose988 = p := Option.some.inj (row988_generated.symm.trans generated)
  subst p
  exact (row988_illegal legal).elim

def rowPose989 : Pose 7 := ⟨perm10, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row989_fields : pairFieldsMatchB 188160 facet0 facet865 key0 key989 rowPose989 = true := by decide +kernel
theorem row989_generated : rootPair 989 = some rowPose989 :=
  pairFieldsMatchB_sound (by decide) row989_fields
theorem row989_source : sourceKey 989 ∈ geometry.profile (sourceOwner 989) := by decide +kernel
theorem row989_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 865 key0).FastValid geometry rowPose989 := by decide +kernel
theorem row989_illegal : ¬ geometry.LegalContact rowPose989 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row989_reject_checked)
theorem row989_classified : RowClassified 989 := by
  intro p generated legal
  have he : rowPose989 = p := Option.some.inj (row989_generated.symm.trans generated)
  subst p
  exact (row989_illegal legal).elim

def rowPose990 : Pose 7 := ⟨perm22, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row990_fields : pairFieldsMatchB 188160 facet0 facet866 key0 key990 rowPose990 = true := by decide +kernel
theorem row990_generated : rootPair 990 = some rowPose990 :=
  pairFieldsMatchB_sound (by decide) row990_fields
theorem row990_source : sourceKey 990 ∈ geometry.profile (sourceOwner 990) := by decide +kernel
theorem row990_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 866 key1).FastValid geometry rowPose990 := by decide +kernel
theorem row990_illegal : ¬ geometry.LegalContact rowPose990 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row990_reject_checked)
theorem row990_classified : RowClassified 990 := by
  intro p generated legal
  have he : rowPose990 = p := Option.some.inj (row990_generated.symm.trans generated)
  subst p
  exact (row990_illegal legal).elim

def rowPose991 : Pose 7 := ⟨perm37, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row991_fields : pairFieldsMatchB 188160 facet0 facet867 key0 key991 rowPose991 = true := by decide +kernel
theorem row991_generated : rootPair 991 = some rowPose991 :=
  pairFieldsMatchB_sound (by decide) row991_fields
theorem row991_source : sourceKey 991 ∈ geometry.profile (sourceOwner 991) := by decide +kernel
theorem row991_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 867 key0).FastValid geometry rowPose991 := by decide +kernel
theorem row991_illegal : ¬ geometry.LegalContact rowPose991 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row991_reject_checked)
theorem row991_classified : RowClassified 991 := by
  intro p generated legal
  have he : rowPose991 = p := Option.some.inj (row991_generated.symm.trans generated)
  subst p
  exact (row991_illegal legal).elim

theorem chunk30_classified (i : Fin 32) : RowClassified ⟨960 + i.val, by omega⟩ := by
  fin_cases i
  · exact row960_classified
  · exact row961_classified
  · exact row962_classified
  · exact row963_classified
  · exact row964_classified
  · exact row965_classified
  · exact row966_classified
  · exact row967_classified
  · exact row968_classified
  · exact row969_classified
  · exact row970_classified
  · exact row971_classified
  · exact row972_classified
  · exact row973_classified
  · exact row974_classified
  · exact row975_classified
  · exact row976_classified
  · exact row977_classified
  · exact row978_classified
  · exact row979_classified
  · exact row980_classified
  · exact row981_classified
  · exact row982_classified
  · exact row983_classified
  · exact row984_classified
  · exact row985_classified
  · exact row986_classified
  · exact row987_classified
  · exact row988_classified
  · exact row989_classified
  · exact row990_classified
  · exact row991_classified

theorem chunk30_source (i : Fin 32) : sourceKey ⟨960 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨960 + i.val, by omega⟩) := by
  fin_cases i
  · exact row960_source
  · exact row961_source
  · exact row962_source
  · exact row963_source
  · exact row964_source
  · exact row965_source
  · exact row966_source
  · exact row967_source
  · exact row968_source
  · exact row969_source
  · exact row970_source
  · exact row971_source
  · exact row972_source
  · exact row973_source
  · exact row974_source
  · exact row975_source
  · exact row976_source
  · exact row977_source
  · exact row978_source
  · exact row979_source
  · exact row980_source
  · exact row981_source
  · exact row982_source
  · exact row983_source
  · exact row984_source
  · exact row985_source
  · exact row986_source
  · exact row987_source
  · exact row988_source
  · exact row989_source
  · exact row990_source
  · exact row991_source

#print axioms chunk30_classified
end SparseMonotiles.Contact.RootZeroPilot7
