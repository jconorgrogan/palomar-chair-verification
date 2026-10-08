module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose992 : Pose 7 := ⟨perm58, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row992_fields : pairFieldsMatchB 188160 facet0 facet868 key0 key992 rowPose992 = true := by decide +kernel
theorem row992_generated : rootPair 992 = some rowPose992 :=
  pairFieldsMatchB_sound (by decide) row992_fields
theorem row992_source : sourceKey 992 ∈ geometry.profile (sourceOwner 992) := by decide +kernel
theorem row992_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 868 key0).FastValid geometry rowPose992 := by decide +kernel
theorem row992_illegal : ¬ geometry.LegalContact rowPose992 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row992_reject_checked)
theorem row992_classified : RowClassified 992 := by
  intro p generated legal
  have he : rowPose992 = p := Option.some.inj (row992_generated.symm.trans generated)
  subst p
  exact (row992_illegal legal).elim

def rowPose993 : Pose 7 := ⟨perm74, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row993_fields : pairFieldsMatchB 188160 facet0 facet869 key0 key993 rowPose993 = true := by decide +kernel
theorem row993_generated : rootPair 993 = some rowPose993 :=
  pairFieldsMatchB_sound (by decide) row993_fields
theorem row993_source : sourceKey 993 ∈ geometry.profile (sourceOwner 993) := by decide +kernel
theorem row993_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 869 key0).FastValid geometry rowPose993 := by decide +kernel
theorem row993_illegal : ¬ geometry.LegalContact rowPose993 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row993_reject_checked)
theorem row993_classified : RowClassified 993 := by
  intro p generated legal
  have he : rowPose993 = p := Option.some.inj (row993_generated.symm.trans generated)
  subst p
  exact (row993_illegal legal).elim

def rowPose994 : Pose 7 := ⟨perm69, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row994_fields : pairFieldsMatchB 188160 facet0 facet869 key0 key994 rowPose994 = true := by decide +kernel
theorem row994_generated : rootPair 994 = some rowPose994 :=
  pairFieldsMatchB_sound (by decide) row994_fields
theorem row994_source : sourceKey 994 ∈ geometry.profile (sourceOwner 994) := by decide +kernel
theorem row994_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 855 key8).FastValid geometry rowPose994 := by decide +kernel
theorem row994_illegal : ¬ geometry.LegalContact rowPose994 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row994_reject_checked)
theorem row994_classified : RowClassified 994 := by
  intro p generated legal
  have he : rowPose994 = p := Option.some.inj (row994_generated.symm.trans generated)
  subst p
  exact (row994_illegal legal).elim

def rowPose995 : Pose 7 := ⟨perm73, ![false, true, false, false, true, false, false], ![-1, 2, -1, -1, 2, -1, -1]⟩
theorem row995_fields : pairFieldsMatchB 188160 facet0 facet870 key0 key995 rowPose995 = true := by decide +kernel
theorem row995_generated : rootPair 995 = some rowPose995 :=
  pairFieldsMatchB_sound (by decide) row995_fields
theorem row995_source : sourceKey 995 ∈ geometry.profile (sourceOwner 995) := by decide +kernel
theorem row995_reject_checked : (show IndexedRejection 7 896 from .overlap ![0, 0, 0, 0, 1, 0, 0]).FastValid geometry rowPose995 := by decide +kernel
theorem row995_illegal : ¬ geometry.LegalContact rowPose995 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row995_reject_checked)
theorem row995_classified : RowClassified 995 := by
  intro p generated legal
  have he : rowPose995 = p := Option.some.inj (row995_generated.symm.trans generated)
  subst p
  exact (row995_illegal legal).elim

def rowPose996 : Pose 7 := ⟨perm87, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row996_fields : pairFieldsMatchB 188160 facet0 facet871 key0 key996 rowPose996 = true := by decide +kernel
theorem row996_generated : rootPair 996 = some rowPose996 :=
  pairFieldsMatchB_sound (by decide) row996_fields
theorem row996_source : sourceKey 996 ∈ geometry.profile (sourceOwner 996) := by decide +kernel
theorem row996_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 871 key1).FastValid geometry rowPose996 := by decide +kernel
theorem row996_illegal : ¬ geometry.LegalContact rowPose996 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row996_reject_checked)
theorem row996_classified : RowClassified 996 := by
  intro p generated legal
  have he : rowPose996 = p := Option.some.inj (row996_generated.symm.trans generated)
  subst p
  exact (row996_illegal legal).elim

def rowPose997 : Pose 7 := ⟨perm96, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row997_fields : pairFieldsMatchB 188160 facet0 facet872 key0 key997 rowPose997 = true := by decide +kernel
theorem row997_generated : rootPair 997 = some rowPose997 :=
  pairFieldsMatchB_sound (by decide) row997_fields
theorem row997_source : sourceKey 997 ∈ geometry.profile (sourceOwner 997) := by decide +kernel
theorem row997_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 872 key1).FastValid geometry rowPose997 := by decide +kernel
theorem row997_illegal : ¬ geometry.LegalContact rowPose997 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row997_reject_checked)
theorem row997_classified : RowClassified 997 := by
  intro p generated legal
  have he : rowPose997 = p := Option.some.inj (row997_generated.symm.trans generated)
  subst p
  exact (row997_illegal legal).elim

def rowPose998 : Pose 7 := ⟨perm15, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row998_fields : pairFieldsMatchB 188160 facet0 facet873 key0 key998 rowPose998 = true := by decide +kernel
theorem row998_generated : rootPair 998 = some rowPose998 :=
  pairFieldsMatchB_sound (by decide) row998_fields
theorem row998_source : sourceKey 998 ∈ geometry.profile (sourceOwner 998) := by decide +kernel
theorem row998_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 873 key1).FastValid geometry rowPose998 := by decide +kernel
theorem row998_illegal : ¬ geometry.LegalContact rowPose998 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row998_reject_checked)
theorem row998_classified : RowClassified 998 := by
  intro p generated legal
  have he : rowPose998 = p := Option.some.inj (row998_generated.symm.trans generated)
  subst p
  exact (row998_illegal legal).elim

def rowPose999 : Pose 7 := ⟨perm24, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row999_fields : pairFieldsMatchB 188160 facet0 facet874 key0 key999 rowPose999 = true := by decide +kernel
theorem row999_generated : rootPair 999 = some rowPose999 :=
  pairFieldsMatchB_sound (by decide) row999_fields
theorem row999_source : sourceKey 999 ∈ geometry.profile (sourceOwner 999) := by decide +kernel
theorem row999_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 874 key1).FastValid geometry rowPose999 := by decide +kernel
theorem row999_illegal : ¬ geometry.LegalContact rowPose999 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row999_reject_checked)
theorem row999_classified : RowClassified 999 := by
  intro p generated legal
  have he : rowPose999 = p := Option.some.inj (row999_generated.symm.trans generated)
  subst p
  exact (row999_illegal legal).elim

def rowPose1000 : Pose 7 := ⟨perm37, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row1000_fields : pairFieldsMatchB 188160 facet0 facet875 key0 key1000 rowPose1000 = true := by decide +kernel
theorem row1000_generated : rootPair 1000 = some rowPose1000 :=
  pairFieldsMatchB_sound (by decide) row1000_fields
theorem row1000_source : sourceKey 1000 ∈ geometry.profile (sourceOwner 1000) := by decide +kernel
theorem row1000_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 875 key0).FastValid geometry rowPose1000 := by decide +kernel
theorem row1000_illegal : ¬ geometry.LegalContact rowPose1000 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1000_reject_checked)
theorem row1000_classified : RowClassified 1000 := by
  intro p generated legal
  have he : rowPose1000 = p := Option.some.inj (row1000_generated.symm.trans generated)
  subst p
  exact (row1000_illegal legal).elim

def rowPose1001 : Pose 7 := ⟨perm42, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row1001_fields : pairFieldsMatchB 188160 facet0 facet875 key0 key1001 rowPose1001 = true := by decide +kernel
theorem row1001_generated : rootPair 1001 = some rowPose1001 :=
  pairFieldsMatchB_sound (by decide) row1001_fields
theorem row1001_source : sourceKey 1001 ∈ geometry.profile (sourceOwner 1001) := by decide +kernel
theorem row1001_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 647 key8).FastValid geometry rowPose1001 := by decide +kernel
theorem row1001_illegal : ¬ geometry.LegalContact rowPose1001 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1001_reject_checked)
theorem row1001_classified : RowClassified 1001 := by
  intro p generated legal
  have he : rowPose1001 = p := Option.some.inj (row1001_generated.symm.trans generated)
  subst p
  exact (row1001_illegal legal).elim

def rowPose1002 : Pose 7 := ⟨perm53, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row1002_fields : pairFieldsMatchB 188160 facet0 facet876 key0 key1002 rowPose1002 = true := by decide +kernel
theorem row1002_generated : rootPair 1002 = some rowPose1002 :=
  pairFieldsMatchB_sound (by decide) row1002_fields
theorem row1002_source : sourceKey 1002 ∈ geometry.profile (sourceOwner 1002) := by decide +kernel
theorem row1002_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 876 key0).FastValid geometry rowPose1002 := by decide +kernel
theorem row1002_illegal : ¬ geometry.LegalContact rowPose1002 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1002_reject_checked)
theorem row1002_classified : RowClassified 1002 := by
  intro p generated legal
  have he : rowPose1002 = p := Option.some.inj (row1002_generated.symm.trans generated)
  subst p
  exact (row1002_illegal legal).elim

def rowPose1003 : Pose 7 := ⟨perm74, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row1003_fields : pairFieldsMatchB 188160 facet0 facet877 key0 key1003 rowPose1003 = true := by decide +kernel
theorem row1003_generated : rootPair 1003 = some rowPose1003 :=
  pairFieldsMatchB_sound (by decide) row1003_fields
theorem row1003_source : sourceKey 1003 ∈ geometry.profile (sourceOwner 1003) := by decide +kernel
theorem row1003_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 877 key0).FastValid geometry rowPose1003 := by decide +kernel
theorem row1003_illegal : ¬ geometry.LegalContact rowPose1003 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1003_reject_checked)
theorem row1003_classified : RowClassified 1003 := by
  intro p generated legal
  have he : rowPose1003 = p := Option.some.inj (row1003_generated.symm.trans generated)
  subst p
  exact (row1003_illegal legal).elim

def rowPose1004 : Pose 7 := ⟨perm89, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row1004_fields : pairFieldsMatchB 188160 facet0 facet878 key0 key1004 rowPose1004 = true := by decide +kernel
theorem row1004_generated : rootPair 1004 = some rowPose1004 :=
  pairFieldsMatchB_sound (by decide) row1004_fields
theorem row1004_source : sourceKey 1004 ∈ geometry.profile (sourceOwner 1004) := by decide +kernel
theorem row1004_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 878 key1).FastValid geometry rowPose1004 := by decide +kernel
theorem row1004_illegal : ¬ geometry.LegalContact rowPose1004 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1004_reject_checked)
theorem row1004_classified : RowClassified 1004 := by
  intro p generated legal
  have he : rowPose1004 = p := Option.some.inj (row1004_generated.symm.trans generated)
  subst p
  exact (row1004_illegal legal).elim

def rowPose1005 : Pose 7 := ⟨perm101, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row1005_fields : pairFieldsMatchB 188160 facet0 facet879 key0 key1005 rowPose1005 = true := by decide +kernel
theorem row1005_generated : rootPair 1005 = some rowPose1005 :=
  pairFieldsMatchB_sound (by decide) row1005_fields
theorem row1005_source : sourceKey 1005 ∈ geometry.profile (sourceOwner 1005) := by decide +kernel
theorem row1005_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 879 key0).FastValid geometry rowPose1005 := by decide +kernel
theorem row1005_illegal : ¬ geometry.LegalContact rowPose1005 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1005_reject_checked)
theorem row1005_classified : RowClassified 1005 := by
  intro p generated legal
  have he : rowPose1005 = p := Option.some.inj (row1005_generated.symm.trans generated)
  subst p
  exact (row1005_illegal legal).elim

def rowPose1006 : Pose 7 := ⟨perm0, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row1006_fields : pairFieldsMatchB 188160 facet0 facet880 key0 key1006 rowPose1006 = true := by decide +kernel
theorem row1006_generated : rootPair 1006 = some rowPose1006 :=
  pairFieldsMatchB_sound (by decide) row1006_fields
theorem row1006_source : sourceKey 1006 ∈ geometry.profile (sourceOwner 1006) := by decide +kernel
theorem row1006_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 880 key1).FastValid geometry rowPose1006 := by decide +kernel
theorem row1006_illegal : ¬ geometry.LegalContact rowPose1006 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1006_reject_checked)
theorem row1006_classified : RowClassified 1006 := by
  intro p generated legal
  have he : rowPose1006 = p := Option.some.inj (row1006_generated.symm.trans generated)
  subst p
  exact (row1006_illegal legal).elim

def rowPose1007 : Pose 7 := ⟨perm16, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row1007_fields : pairFieldsMatchB 188160 facet0 facet881 key0 key1007 rowPose1007 = true := by decide +kernel
theorem row1007_generated : rootPair 1007 = some rowPose1007 :=
  pairFieldsMatchB_sound (by decide) row1007_fields
theorem row1007_source : sourceKey 1007 ∈ geometry.profile (sourceOwner 1007) := by decide +kernel
theorem row1007_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 881 key0).FastValid geometry rowPose1007 := by decide +kernel
theorem row1007_illegal : ¬ geometry.LegalContact rowPose1007 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1007_reject_checked)
theorem row1007_classified : RowClassified 1007 := by
  intro p generated legal
  have he : rowPose1007 = p := Option.some.inj (row1007_generated.symm.trans generated)
  subst p
  exact (row1007_illegal legal).elim

def rowPose1008 : Pose 7 := ⟨perm40, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row1008_fields : pairFieldsMatchB 188160 facet0 facet882 key0 key1008 rowPose1008 = true := by decide +kernel
theorem row1008_generated : rootPair 1008 = some rowPose1008 :=
  pairFieldsMatchB_sound (by decide) row1008_fields
theorem row1008_source : sourceKey 1008 ∈ geometry.profile (sourceOwner 1008) := by decide +kernel
theorem row1008_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 882 key1).FastValid geometry rowPose1008 := by decide +kernel
theorem row1008_illegal : ¬ geometry.LegalContact rowPose1008 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1008_reject_checked)
theorem row1008_classified : RowClassified 1008 := by
  intro p generated legal
  have he : rowPose1008 = p := Option.some.inj (row1008_generated.symm.trans generated)
  subst p
  exact (row1008_illegal legal).elim

def rowPose1009 : Pose 7 := ⟨perm53, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row1009_fields : pairFieldsMatchB 188160 facet0 facet883 key0 key1009 rowPose1009 = true := by decide +kernel
theorem row1009_generated : rootPair 1009 = some rowPose1009 :=
  pairFieldsMatchB_sound (by decide) row1009_fields
theorem row1009_source : sourceKey 1009 ∈ geometry.profile (sourceOwner 1009) := by decide +kernel
theorem row1009_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 883 key0).FastValid geometry rowPose1009 := by decide +kernel
theorem row1009_illegal : ¬ geometry.LegalContact rowPose1009 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1009_reject_checked)
theorem row1009_classified : RowClassified 1009 := by
  intro p generated legal
  have he : rowPose1009 = p := Option.some.inj (row1009_generated.symm.trans generated)
  subst p
  exact (row1009_illegal legal).elim

def rowPose1010 : Pose 7 := ⟨perm74, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row1010_fields : pairFieldsMatchB 188160 facet0 facet884 key0 key1010 rowPose1010 = true := by decide +kernel
theorem row1010_generated : rootPair 1010 = some rowPose1010 :=
  pairFieldsMatchB_sound (by decide) row1010_fields
theorem row1010_source : sourceKey 1010 ∈ geometry.profile (sourceOwner 1010) := by decide +kernel
theorem row1010_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 884 key0).FastValid geometry rowPose1010 := by decide +kernel
theorem row1010_illegal : ¬ geometry.LegalContact rowPose1010 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1010_reject_checked)
theorem row1010_classified : RowClassified 1010 := by
  intro p generated legal
  have he : rowPose1010 = p := Option.some.inj (row1010_generated.symm.trans generated)
  subst p
  exact (row1010_illegal legal).elim

def rowPose1011 : Pose 7 := ⟨perm90, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row1011_fields : pairFieldsMatchB 188160 facet0 facet885 key0 key1011 rowPose1011 = true := by decide +kernel
theorem row1011_generated : rootPair 1011 = some rowPose1011 :=
  pairFieldsMatchB_sound (by decide) row1011_fields
theorem row1011_source : sourceKey 1011 ∈ geometry.profile (sourceOwner 1011) := by decide +kernel
theorem row1011_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 885 key0).FastValid geometry rowPose1011 := by decide +kernel
theorem row1011_illegal : ¬ geometry.LegalContact rowPose1011 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1011_reject_checked)
theorem row1011_classified : RowClassified 1011 := by
  intro p generated legal
  have he : rowPose1011 = p := Option.some.inj (row1011_generated.symm.trans generated)
  subst p
  exact (row1011_illegal legal).elim

def rowPose1012 : Pose 7 := ⟨perm87, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row1012_fields : pairFieldsMatchB 188160 facet0 facet885 key0 key1012 rowPose1012 = true := by decide +kernel
theorem row1012_generated : rootPair 1012 = some rowPose1012 :=
  pairFieldsMatchB_sound (by decide) row1012_fields
theorem row1012_source : sourceKey 1012 ∈ geometry.profile (sourceOwner 1012) := by decide +kernel
theorem row1012_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 878 key8).FastValid geometry rowPose1012 := by decide +kernel
theorem row1012_illegal : ¬ geometry.LegalContact rowPose1012 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1012_reject_checked)
theorem row1012_classified : RowClassified 1012 := by
  intro p generated legal
  have he : rowPose1012 = p := Option.some.inj (row1012_generated.symm.trans generated)
  subst p
  exact (row1012_illegal legal).elim

def rowPose1013 : Pose 7 := ⟨perm87, ![false, true, false, false, false, true, true], ![-1, 2, -1, -1, -1, 2, 2]⟩
theorem row1013_fields : pairFieldsMatchB 188160 facet0 facet886 key0 key1013 rowPose1013 = true := by decide +kernel
theorem row1013_generated : rootPair 1013 = some rowPose1013 :=
  pairFieldsMatchB_sound (by decide) row1013_fields
theorem row1013_source : sourceKey 1013 ∈ geometry.profile (sourceOwner 1013) := by decide +kernel
theorem row1013_reject_checked : (show IndexedRejection 7 896 from .overlap ![0, 1, 0, 0, 0, 1, 0]).FastValid geometry rowPose1013 := by decide +kernel
theorem row1013_illegal : ¬ geometry.LegalContact rowPose1013 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1013_reject_checked)
theorem row1013_classified : RowClassified 1013 := by
  intro p generated legal
  have he : rowPose1013 = p := Option.some.inj (row1013_generated.symm.trans generated)
  subst p
  exact (row1013_illegal legal).elim

def rowPose1014 : Pose 7 := ⟨perm111, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row1014_fields : pairFieldsMatchB 188160 facet0 facet887 key0 key1014 rowPose1014 = true := by decide +kernel
theorem row1014_generated : rootPair 1014 = some rowPose1014 :=
  pairFieldsMatchB_sound (by decide) row1014_fields
theorem row1014_source : sourceKey 1014 ∈ geometry.profile (sourceOwner 1014) := by decide +kernel
theorem row1014_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 887 key1).FastValid geometry rowPose1014 := by decide +kernel
theorem row1014_illegal : ¬ geometry.LegalContact rowPose1014 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1014_reject_checked)
theorem row1014_classified : RowClassified 1014 := by
  intro p generated legal
  have he : rowPose1014 = p := Option.some.inj (row1014_generated.symm.trans generated)
  subst p
  exact (row1014_illegal legal).elim

def rowPose1015 : Pose 7 := ⟨perm15, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row1015_fields : pairFieldsMatchB 188160 facet0 facet888 key0 key1015 rowPose1015 = true := by decide +kernel
theorem row1015_generated : rootPair 1015 = some rowPose1015 :=
  pairFieldsMatchB_sound (by decide) row1015_fields
theorem row1015_source : sourceKey 1015 ∈ geometry.profile (sourceOwner 1015) := by decide +kernel
theorem row1015_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 888 key1).FastValid geometry rowPose1015 := by decide +kernel
theorem row1015_illegal : ¬ geometry.LegalContact rowPose1015 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1015_reject_checked)
theorem row1015_classified : RowClassified 1015 := by
  intro p generated legal
  have he : rowPose1015 = p := Option.some.inj (row1015_generated.symm.trans generated)
  subst p
  exact (row1015_illegal legal).elim

def rowPose1016 : Pose 7 := ⟨perm24, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row1016_fields : pairFieldsMatchB 188160 facet0 facet889 key0 key1016 rowPose1016 = true := by decide +kernel
theorem row1016_generated : rootPair 1016 = some rowPose1016 :=
  pairFieldsMatchB_sound (by decide) row1016_fields
theorem row1016_source : sourceKey 1016 ∈ geometry.profile (sourceOwner 1016) := by decide +kernel
theorem row1016_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 889 key1).FastValid geometry rowPose1016 := by decide +kernel
theorem row1016_illegal : ¬ geometry.LegalContact rowPose1016 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1016_reject_checked)
theorem row1016_classified : RowClassified 1016 := by
  intro p generated legal
  have he : rowPose1016 = p := Option.some.inj (row1016_generated.symm.trans generated)
  subst p
  exact (row1016_illegal legal).elim

def rowPose1017 : Pose 7 := ⟨perm38, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row1017_fields : pairFieldsMatchB 188160 facet0 facet890 key0 key1017 rowPose1017 = true := by decide +kernel
theorem row1017_generated : rootPair 1017 = some rowPose1017 :=
  pairFieldsMatchB_sound (by decide) row1017_fields
theorem row1017_source : sourceKey 1017 ∈ geometry.profile (sourceOwner 1017) := by decide +kernel
theorem row1017_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 890 key0).FastValid geometry rowPose1017 := by decide +kernel
theorem row1017_illegal : ¬ geometry.LegalContact rowPose1017 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1017_reject_checked)
theorem row1017_classified : RowClassified 1017 := by
  intro p generated legal
  have he : rowPose1017 = p := Option.some.inj (row1017_generated.symm.trans generated)
  subst p
  exact (row1017_illegal legal).elim

def rowPose1018 : Pose 7 := ⟨perm56, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row1018_fields : pairFieldsMatchB 188160 facet0 facet891 key0 key1018 rowPose1018 = true := by decide +kernel
theorem row1018_generated : rootPair 1018 = some rowPose1018 :=
  pairFieldsMatchB_sound (by decide) row1018_fields
theorem row1018_source : sourceKey 1018 ∈ geometry.profile (sourceOwner 1018) := by decide +kernel
theorem row1018_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 891 key1).FastValid geometry rowPose1018 := by decide +kernel
theorem row1018_illegal : ¬ geometry.LegalContact rowPose1018 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1018_reject_checked)
theorem row1018_classified : RowClassified 1018 := by
  intro p generated legal
  have he : rowPose1018 = p := Option.some.inj (row1018_generated.symm.trans generated)
  subst p
  exact (row1018_illegal legal).elim

def rowPose1019 : Pose 7 := ⟨perm69, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row1019_fields : pairFieldsMatchB 188160 facet0 facet892 key0 key1019 rowPose1019 = true := by decide +kernel
theorem row1019_generated : rootPair 1019 = some rowPose1019 :=
  pairFieldsMatchB_sound (by decide) row1019_fields
theorem row1019_source : sourceKey 1019 ∈ geometry.profile (sourceOwner 1019) := by decide +kernel
theorem row1019_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 892 key0).FastValid geometry rowPose1019 := by decide +kernel
theorem row1019_illegal : ¬ geometry.LegalContact rowPose1019 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1019_reject_checked)
theorem row1019_classified : RowClassified 1019 := by
  intro p generated legal
  have he : rowPose1019 = p := Option.some.inj (row1019_generated.symm.trans generated)
  subst p
  exact (row1019_illegal legal).elim

def rowPose1020 : Pose 7 := ⟨perm90, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row1020_fields : pairFieldsMatchB 188160 facet0 facet893 key0 key1020 rowPose1020 = true := by decide +kernel
theorem row1020_generated : rootPair 1020 = some rowPose1020 :=
  pairFieldsMatchB_sound (by decide) row1020_fields
theorem row1020_source : sourceKey 1020 ∈ geometry.profile (sourceOwner 1020) := by decide +kernel
theorem row1020_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 893 key0).FastValid geometry rowPose1020 := by decide +kernel
theorem row1020_illegal : ¬ geometry.LegalContact rowPose1020 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1020_reject_checked)
theorem row1020_classified : RowClassified 1020 := by
  intro p generated legal
  have he : rowPose1020 = p := Option.some.inj (row1020_generated.symm.trans generated)
  subst p
  exact (row1020_illegal legal).elim

def rowPose1021 : Pose 7 := ⟨perm96, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row1021_fields : pairFieldsMatchB 188160 facet0 facet894 key0 key1021 rowPose1021 = true := by decide +kernel
theorem row1021_generated : rootPair 1021 = some rowPose1021 :=
  pairFieldsMatchB_sound (by decide) row1021_fields
theorem row1021_source : sourceKey 1021 ∈ geometry.profile (sourceOwner 1021) := by decide +kernel
theorem row1021_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 894 key0).FastValid geometry rowPose1021 := by decide +kernel
theorem row1021_illegal : ¬ geometry.LegalContact rowPose1021 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1021_reject_checked)
theorem row1021_classified : RowClassified 1021 := by
  intro p generated legal
  have he : rowPose1021 = p := Option.some.inj (row1021_generated.symm.trans generated)
  subst p
  exact (row1021_illegal legal).elim

def rowPose1022 : Pose 7 := ⟨perm111, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row1022_fields : pairFieldsMatchB 188160 facet0 facet894 key0 key1022 rowPose1022 = true := by decide +kernel
theorem row1022_generated : rootPair 1022 = some rowPose1022 :=
  pairFieldsMatchB_sound (by decide) row1022_fields
theorem row1022_source : sourceKey 1022 ∈ geometry.profile (sourceOwner 1022) := by decide +kernel
theorem row1022_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 440 key8).FastValid geometry rowPose1022 := by decide +kernel
theorem row1022_illegal : ¬ geometry.LegalContact rowPose1022 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1022_reject_checked)
theorem row1022_classified : RowClassified 1022 := by
  intro p generated legal
  have he : rowPose1022 = p := Option.some.inj (row1022_generated.symm.trans generated)
  subst p
  exact (row1022_illegal legal).elim

def rowPose1023 : Pose 7 := ⟨perm96, ![false, true, false, false, true, true, true], ![-1, 2, -1, -1, 2, 2, 2]⟩
theorem row1023_fields : pairFieldsMatchB 188160 facet0 facet895 key0 key1023 rowPose1023 = true := by decide +kernel
theorem row1023_generated : rootPair 1023 = some rowPose1023 :=
  pairFieldsMatchB_sound (by decide) row1023_fields
theorem row1023_source : sourceKey 1023 ∈ geometry.profile (sourceOwner 1023) := by decide +kernel
theorem row1023_reject_checked : (show IndexedRejection 7 896 from .overlap ![0, 0, 0, 0, 1, 0, 0]).FastValid geometry rowPose1023 := by decide +kernel
theorem row1023_illegal : ¬ geometry.LegalContact rowPose1023 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row1023_reject_checked)
theorem row1023_classified : RowClassified 1023 := by
  intro p generated legal
  have he : rowPose1023 = p := Option.some.inj (row1023_generated.symm.trans generated)
  subst p
  exact (row1023_illegal legal).elim

theorem chunk31_classified (i : Fin 32) : RowClassified ⟨992 + i.val, by omega⟩ := by
  fin_cases i
  · exact row992_classified
  · exact row993_classified
  · exact row994_classified
  · exact row995_classified
  · exact row996_classified
  · exact row997_classified
  · exact row998_classified
  · exact row999_classified
  · exact row1000_classified
  · exact row1001_classified
  · exact row1002_classified
  · exact row1003_classified
  · exact row1004_classified
  · exact row1005_classified
  · exact row1006_classified
  · exact row1007_classified
  · exact row1008_classified
  · exact row1009_classified
  · exact row1010_classified
  · exact row1011_classified
  · exact row1012_classified
  · exact row1013_classified
  · exact row1014_classified
  · exact row1015_classified
  · exact row1016_classified
  · exact row1017_classified
  · exact row1018_classified
  · exact row1019_classified
  · exact row1020_classified
  · exact row1021_classified
  · exact row1022_classified
  · exact row1023_classified

theorem chunk31_source (i : Fin 32) : sourceKey ⟨992 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨992 + i.val, by omega⟩) := by
  fin_cases i
  · exact row992_source
  · exact row993_source
  · exact row994_source
  · exact row995_source
  · exact row996_source
  · exact row997_source
  · exact row998_source
  · exact row999_source
  · exact row1000_source
  · exact row1001_source
  · exact row1002_source
  · exact row1003_source
  · exact row1004_source
  · exact row1005_source
  · exact row1006_source
  · exact row1007_source
  · exact row1008_source
  · exact row1009_source
  · exact row1010_source
  · exact row1011_source
  · exact row1012_source
  · exact row1013_source
  · exact row1014_source
  · exact row1015_source
  · exact row1016_source
  · exact row1017_source
  · exact row1018_source
  · exact row1019_source
  · exact row1020_source
  · exact row1021_source
  · exact row1022_source
  · exact row1023_source

#print axioms chunk31_classified
end SparseMonotiles.Contact.RootZeroPilot7
