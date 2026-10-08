module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose928 : Pose 7 := ⟨perm55, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row928_fields : pairFieldsMatchB 188160 facet0 facet811 key0 key928 rowPose928 = true := by decide +kernel
theorem row928_generated : rootPair 928 = some rowPose928 :=
  pairFieldsMatchB_sound (by decide) row928_fields
theorem row928_source : sourceKey 928 ∈ geometry.profile (sourceOwner 928) := by decide +kernel
theorem row928_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 811 key1).FastValid geometry rowPose928 := by decide +kernel
theorem row928_illegal : ¬ geometry.LegalContact rowPose928 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row928_reject_checked)
theorem row928_classified : RowClassified 928 := by
  intro p generated legal
  have he : rowPose928 = p := Option.some.inj (row928_generated.symm.trans generated)
  subst p
  exact (row928_illegal legal).elim

def rowPose929 : Pose 7 := ⟨perm73, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row929_fields : pairFieldsMatchB 188160 facet0 facet812 key0 key929 rowPose929 = true := by decide +kernel
theorem row929_generated : rootPair 929 = some rowPose929 :=
  pairFieldsMatchB_sound (by decide) row929_fields
theorem row929_source : sourceKey 929 ∈ geometry.profile (sourceOwner 929) := by decide +kernel
theorem row929_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 812 key0).FastValid geometry rowPose929 := by decide +kernel
theorem row929_illegal : ¬ geometry.LegalContact rowPose929 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row929_reject_checked)
theorem row929_classified : RowClassified 929 := by
  intro p generated legal
  have he : rowPose929 = p := Option.some.inj (row929_generated.symm.trans generated)
  subst p
  exact (row929_illegal legal).elim

def rowPose930 : Pose 7 := ⟨perm87, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row930_fields : pairFieldsMatchB 188160 facet0 facet813 key0 key930 rowPose930 = true := by decide +kernel
theorem row930_generated : rootPair 930 = some rowPose930 :=
  pairFieldsMatchB_sound (by decide) row930_fields
theorem row930_source : sourceKey 930 ∈ geometry.profile (sourceOwner 930) := by decide +kernel
theorem row930_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 813 key1).FastValid geometry rowPose930 := by decide +kernel
theorem row930_illegal : ¬ geometry.LegalContact rowPose930 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row930_reject_checked)
theorem row930_classified : RowClassified 930 := by
  intro p generated legal
  have he : rowPose930 = p := Option.some.inj (row930_generated.symm.trans generated)
  subst p
  exact (row930_illegal legal).elim

def rowPose931 : Pose 7 := ⟨perm96, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row931_fields : pairFieldsMatchB 188160 facet0 facet814 key0 key931 rowPose931 = true := by decide +kernel
theorem row931_generated : rootPair 931 = some rowPose931 :=
  pairFieldsMatchB_sound (by decide) row931_fields
theorem row931_source : sourceKey 931 ∈ geometry.profile (sourceOwner 931) := by decide +kernel
theorem row931_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 814 key1).FastValid geometry rowPose931 := by decide +kernel
theorem row931_illegal : ¬ geometry.LegalContact rowPose931 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row931_reject_checked)
theorem row931_classified : RowClassified 931 := by
  intro p generated legal
  have he : rowPose931 = p := Option.some.inj (row931_generated.symm.trans generated)
  subst p
  exact (row931_illegal legal).elim

def rowPose932 : Pose 7 := ⟨perm0, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row932_fields : pairFieldsMatchB 188160 facet0 facet815 key0 key932 rowPose932 = true := by decide +kernel
theorem row932_generated : rootPair 932 = some rowPose932 :=
  pairFieldsMatchB_sound (by decide) row932_fields
theorem row932_source : sourceKey 932 ∈ geometry.profile (sourceOwner 932) := by decide +kernel
theorem row932_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 815 key0).FastValid geometry rowPose932 := by decide +kernel
theorem row932_illegal : ¬ geometry.LegalContact rowPose932 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row932_reject_checked)
theorem row932_classified : RowClassified 932 := by
  intro p generated legal
  have he : rowPose932 = p := Option.some.inj (row932_generated.symm.trans generated)
  subst p
  exact (row932_illegal legal).elim

def rowPose933 : Pose 7 := ⟨perm15, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row933_fields : pairFieldsMatchB 188160 facet0 facet815 key0 key933 rowPose933 = true := by decide +kernel
theorem row933_generated : rootPair 933 = some rowPose933 :=
  pairFieldsMatchB_sound (by decide) row933_fields
theorem row933_source : sourceKey 933 ∈ geometry.profile (sourceOwner 933) := by decide +kernel
theorem row933_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 589 key8).FastValid geometry rowPose933 := by decide +kernel
theorem row933_illegal : ¬ geometry.LegalContact rowPose933 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row933_reject_checked)
theorem row933_classified : RowClassified 933 := by
  intro p generated legal
  have he : rowPose933 = p := Option.some.inj (row933_generated.symm.trans generated)
  subst p
  exact (row933_illegal legal).elim

def rowPose934 : Pose 7 := ⟨perm21, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row934_fields : pairFieldsMatchB 188160 facet0 facet816 key0 key934 rowPose934 = true := by decide +kernel
theorem row934_generated : rootPair 934 = some rowPose934 :=
  pairFieldsMatchB_sound (by decide) row934_fields
theorem row934_source : sourceKey 934 ∈ geometry.profile (sourceOwner 934) := by decide +kernel
theorem row934_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 816 key1).FastValid geometry rowPose934 := by decide +kernel
theorem row934_illegal : ¬ geometry.LegalContact rowPose934 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row934_reject_checked)
theorem row934_classified : RowClassified 934 := by
  intro p generated legal
  have he : rowPose934 = p := Option.some.inj (row934_generated.symm.trans generated)
  subst p
  exact (row934_illegal legal).elim

def rowPose935 : Pose 7 := ⟨perm42, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row935_fields : pairFieldsMatchB 188160 facet0 facet817 key0 key935 rowPose935 = true := by decide +kernel
theorem row935_generated : rootPair 935 = some rowPose935 :=
  pairFieldsMatchB_sound (by decide) row935_fields
theorem row935_source : sourceKey 935 ∈ geometry.profile (sourceOwner 935) := by decide +kernel
theorem row935_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 817 key1).FastValid geometry rowPose935 := by decide +kernel
theorem row935_illegal : ¬ geometry.LegalContact rowPose935 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row935_reject_checked)
theorem row935_classified : RowClassified 935 := by
  intro p generated legal
  have he : rowPose935 = p := Option.some.inj (row935_generated.symm.trans generated)
  subst p
  exact (row935_illegal legal).elim

def rowPose936 : Pose 7 := ⟨perm55, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row936_fields : pairFieldsMatchB 188160 facet0 facet818 key0 key936 rowPose936 = true := by decide +kernel
theorem row936_generated : rootPair 936 = some rowPose936 :=
  pairFieldsMatchB_sound (by decide) row936_fields
theorem row936_source : sourceKey 936 ∈ geometry.profile (sourceOwner 936) := by decide +kernel
theorem row936_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 818 key0).FastValid geometry rowPose936 := by decide +kernel
theorem row936_illegal : ¬ geometry.LegalContact rowPose936 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row936_reject_checked)
theorem row936_classified : RowClassified 936 := by
  intro p generated legal
  have he : rowPose936 = p := Option.some.inj (row936_generated.symm.trans generated)
  subst p
  exact (row936_illegal legal).elim

def rowPose937 : Pose 7 := ⟨perm73, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row937_fields : pairFieldsMatchB 188160 facet0 facet819 key0 key937 rowPose937 = true := by decide +kernel
theorem row937_generated : rootPair 937 = some rowPose937 :=
  pairFieldsMatchB_sound (by decide) row937_fields
theorem row937_source : sourceKey 937 ∈ geometry.profile (sourceOwner 937) := by decide +kernel
theorem row937_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 819 key1).FastValid geometry rowPose937 := by decide +kernel
theorem row937_illegal : ¬ geometry.LegalContact rowPose937 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row937_reject_checked)
theorem row937_classified : RowClassified 937 := by
  intro p generated legal
  have he : rowPose937 = p := Option.some.inj (row937_generated.symm.trans generated)
  subst p
  exact (row937_illegal legal).elim

def rowPose938 : Pose 7 := ⟨perm87, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row938_fields : pairFieldsMatchB 188160 facet0 facet820 key0 key938 rowPose938 = true := by decide +kernel
theorem row938_generated : rootPair 938 = some rowPose938 :=
  pairFieldsMatchB_sound (by decide) row938_fields
theorem row938_source : sourceKey 938 ∈ geometry.profile (sourceOwner 938) := by decide +kernel
theorem row938_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 820 key0).FastValid geometry rowPose938 := by decide +kernel
theorem row938_illegal : ¬ geometry.LegalContact rowPose938 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row938_reject_checked)
theorem row938_classified : RowClassified 938 := by
  intro p generated legal
  have he : rowPose938 = p := Option.some.inj (row938_generated.symm.trans generated)
  subst p
  exact (row938_illegal legal).elim

def rowPose939 : Pose 7 := ⟨perm96, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row939_fields : pairFieldsMatchB 188160 facet0 facet821 key0 key939 rowPose939 = true := by decide +kernel
theorem row939_generated : rootPair 939 = some rowPose939 :=
  pairFieldsMatchB_sound (by decide) row939_fields
theorem row939_source : sourceKey 939 ∈ geometry.profile (sourceOwner 939) := by decide +kernel
theorem row939_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 821 key0).FastValid geometry rowPose939 := by decide +kernel
theorem row939_illegal : ¬ geometry.LegalContact rowPose939 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row939_reject_checked)
theorem row939_classified : RowClassified 939 := by
  intro p generated legal
  have he : rowPose939 = p := Option.some.inj (row939_generated.symm.trans generated)
  subst p
  exact (row939_illegal legal).elim

def rowPose940 : Pose 7 := ⟨perm10, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row940_fields : pairFieldsMatchB 188160 facet0 facet822 key0 key940 rowPose940 = true := by decide +kernel
theorem row940_generated : rootPair 940 = some rowPose940 :=
  pairFieldsMatchB_sound (by decide) row940_fields
theorem row940_source : sourceKey 940 ∈ geometry.profile (sourceOwner 940) := by decide +kernel
theorem row940_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 822 key1).FastValid geometry rowPose940 := by decide +kernel
theorem row940_illegal : ¬ geometry.LegalContact rowPose940 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row940_reject_checked)
theorem row940_classified : RowClassified 940 := by
  intro p generated legal
  have he : rowPose940 = p := Option.some.inj (row940_generated.symm.trans generated)
  subst p
  exact (row940_illegal legal).elim

def rowPose941 : Pose 7 := ⟨perm22, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row941_fields : pairFieldsMatchB 188160 facet0 facet823 key0 key941 rowPose941 = true := by decide +kernel
theorem row941_generated : rootPair 941 = some rowPose941 :=
  pairFieldsMatchB_sound (by decide) row941_fields
theorem row941_source : sourceKey 941 ∈ geometry.profile (sourceOwner 941) := by decide +kernel
theorem row941_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 823 key0).FastValid geometry rowPose941 := by decide +kernel
theorem row941_illegal : ¬ geometry.LegalContact rowPose941 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row941_reject_checked)
theorem row941_classified : RowClassified 941 := by
  intro p generated legal
  have he : rowPose941 = p := Option.some.inj (row941_generated.symm.trans generated)
  subst p
  exact (row941_illegal legal).elim

def rowPose942 : Pose 7 := ⟨perm37, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row942_fields : pairFieldsMatchB 188160 facet0 facet824 key0 key942 rowPose942 = true := by decide +kernel
theorem row942_generated : rootPair 942 = some rowPose942 :=
  pairFieldsMatchB_sound (by decide) row942_fields
theorem row942_source : sourceKey 942 ∈ geometry.profile (sourceOwner 942) := by decide +kernel
theorem row942_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 824 key1).FastValid geometry rowPose942 := by decide +kernel
theorem row942_illegal : ¬ geometry.LegalContact rowPose942 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row942_reject_checked)
theorem row942_classified : RowClassified 942 := by
  intro p generated legal
  have he : rowPose942 = p := Option.some.inj (row942_generated.symm.trans generated)
  subst p
  exact (row942_illegal legal).elim

def rowPose943 : Pose 7 := ⟨perm58, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row943_fields : pairFieldsMatchB 188160 facet0 facet825 key0 key943 rowPose943 = true := by decide +kernel
theorem row943_generated : rootPair 943 = some rowPose943 :=
  pairFieldsMatchB_sound (by decide) row943_fields
theorem row943_source : sourceKey 943 ∈ geometry.profile (sourceOwner 943) := by decide +kernel
theorem row943_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 825 key1).FastValid geometry rowPose943 := by decide +kernel
theorem row943_illegal : ¬ geometry.LegalContact rowPose943 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row943_reject_checked)
theorem row943_classified : RowClassified 943 := by
  intro p generated legal
  have he : rowPose943 = p := Option.some.inj (row943_generated.symm.trans generated)
  subst p
  exact (row943_illegal legal).elim

def rowPose944 : Pose 7 := ⟨perm74, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row944_fields : pairFieldsMatchB 188160 facet0 facet826 key0 key944 rowPose944 = true := by decide +kernel
theorem row944_generated : rootPair 944 = some rowPose944 :=
  pairFieldsMatchB_sound (by decide) row944_fields
theorem row944_source : sourceKey 944 ∈ geometry.profile (sourceOwner 944) := by decide +kernel
theorem row944_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 884 key8).FastValid geometry rowPose944 := by decide +kernel
theorem row944_illegal : ¬ geometry.LegalContact rowPose944 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row944_reject_checked)
theorem row944_classified : RowClassified 944 := by
  intro p generated legal
  have he : rowPose944 = p := Option.some.inj (row944_generated.symm.trans generated)
  subst p
  exact (row944_illegal legal).elim

def rowPose945 : Pose 7 := ⟨perm69, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row945_fields : pairFieldsMatchB 188160 facet0 facet826 key0 key945 rowPose945 = true := by decide +kernel
theorem row945_generated : rootPair 945 = some rowPose945 :=
  pairFieldsMatchB_sound (by decide) row945_fields
theorem row945_source : sourceKey 945 ∈ geometry.profile (sourceOwner 945) := by decide +kernel
theorem row945_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 826 key0).FastValid geometry rowPose945 := by decide +kernel
theorem row945_illegal : ¬ geometry.LegalContact rowPose945 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row945_reject_checked)
theorem row945_classified : RowClassified 945 := by
  intro p generated legal
  have he : rowPose945 = p := Option.some.inj (row945_generated.symm.trans generated)
  subst p
  exact (row945_illegal legal).elim

def rowPose946 : Pose 7 := ⟨perm87, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row946_fields : pairFieldsMatchB 188160 facet0 facet827 key0 key946 rowPose946 = true := by decide +kernel
theorem row946_generated : rootPair 946 = some rowPose946 :=
  pairFieldsMatchB_sound (by decide) row946_fields
theorem row946_source : sourceKey 946 ∈ geometry.profile (sourceOwner 946) := by decide +kernel
theorem row946_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 827 key0).FastValid geometry rowPose946 := by decide +kernel
theorem row946_illegal : ¬ geometry.LegalContact rowPose946 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row946_reject_checked)
theorem row946_classified : RowClassified 946 := by
  intro p generated legal
  have he : rowPose946 = p := Option.some.inj (row946_generated.symm.trans generated)
  subst p
  exact (row946_illegal legal).elim

def rowPose947 : Pose 7 := ⟨perm96, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row947_fields : pairFieldsMatchB 188160 facet0 facet828 key0 key947 rowPose947 = true := by decide +kernel
theorem row947_generated : rootPair 947 = some rowPose947 :=
  pairFieldsMatchB_sound (by decide) row947_fields
theorem row947_source : sourceKey 947 ∈ geometry.profile (sourceOwner 947) := by decide +kernel
theorem row947_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 828 key0).FastValid geometry rowPose947 := by decide +kernel
theorem row947_illegal : ¬ geometry.LegalContact rowPose947 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row947_reject_checked)
theorem row947_classified : RowClassified 947 := by
  intro p generated legal
  have he : rowPose947 = p := Option.some.inj (row947_generated.symm.trans generated)
  subst p
  exact (row947_illegal legal).elim

def rowPose948 : Pose 7 := ⟨perm0, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row948_fields : pairFieldsMatchB 188160 facet0 facet829 key0 key948 rowPose948 = true := by decide +kernel
theorem row948_generated : rootPair 948 = some rowPose948 :=
  pairFieldsMatchB_sound (by decide) row948_fields
theorem row948_source : sourceKey 948 ∈ geometry.profile (sourceOwner 948) := by decide +kernel
theorem row948_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 829 key1).FastValid geometry rowPose948 := by decide +kernel
theorem row948_illegal : ¬ geometry.LegalContact rowPose948 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row948_reject_checked)
theorem row948_classified : RowClassified 948 := by
  intro p generated legal
  have he : rowPose948 = p := Option.some.inj (row948_generated.symm.trans generated)
  subst p
  exact (row948_illegal legal).elim

def rowPose949 : Pose 7 := ⟨perm21, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row949_fields : pairFieldsMatchB 188160 facet0 facet830 key0 key949 rowPose949 = true := by decide +kernel
theorem row949_generated : rootPair 949 = some rowPose949 :=
  pairFieldsMatchB_sound (by decide) row949_fields
theorem row949_source : sourceKey 949 ∈ geometry.profile (sourceOwner 949) := by decide +kernel
theorem row949_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 830 key0).FastValid geometry rowPose949 := by decide +kernel
theorem row949_illegal : ¬ geometry.LegalContact rowPose949 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row949_reject_checked)
theorem row949_classified : RowClassified 949 := by
  intro p generated legal
  have he : rowPose949 = p := Option.some.inj (row949_generated.symm.trans generated)
  subst p
  exact (row949_illegal legal).elim

def rowPose950 : Pose 7 := ⟨perm24, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row950_fields : pairFieldsMatchB 188160 facet0 facet830 key0 key950 rowPose950 = true := by decide +kernel
theorem row950_generated : rootPair 950 = some rowPose950 :=
  pairFieldsMatchB_sound (by decide) row950_fields
theorem row950_source : sourceKey 950 ∈ geometry.profile (sourceOwner 950) := by decide +kernel
theorem row950_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 379 key8).FastValid geometry rowPose950 := by decide +kernel
theorem row950_illegal : ¬ geometry.LegalContact rowPose950 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row950_reject_checked)
theorem row950_classified : RowClassified 950 := by
  intro p generated legal
  have he : rowPose950 = p := Option.some.inj (row950_generated.symm.trans generated)
  subst p
  exact (row950_illegal legal).elim

def rowPose951 : Pose 7 := ⟨perm37, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row951_fields : pairFieldsMatchB 188160 facet0 facet831 key0 key951 rowPose951 = true := by decide +kernel
theorem row951_generated : rootPair 951 = some rowPose951 :=
  pairFieldsMatchB_sound (by decide) row951_fields
theorem row951_source : sourceKey 951 ∈ geometry.profile (sourceOwner 951) := by decide +kernel
theorem row951_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 831 key0).FastValid geometry rowPose951 := by decide +kernel
theorem row951_illegal : ¬ geometry.LegalContact rowPose951 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row951_reject_checked)
theorem row951_classified : RowClassified 951 := by
  intro p generated legal
  have he : rowPose951 = p := Option.some.inj (row951_generated.symm.trans generated)
  subst p
  exact (row951_illegal legal).elim

def rowPose952 : Pose 7 := ⟨perm58, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row952_fields : pairFieldsMatchB 188160 facet0 facet832 key0 key952 rowPose952 = true := by decide +kernel
theorem row952_generated : rootPair 952 = some rowPose952 :=
  pairFieldsMatchB_sound (by decide) row952_fields
theorem row952_source : sourceKey 952 ∈ geometry.profile (sourceOwner 952) := by decide +kernel
theorem row952_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 832 key0).FastValid geometry rowPose952 := by decide +kernel
theorem row952_illegal : ¬ geometry.LegalContact rowPose952 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row952_reject_checked)
theorem row952_classified : RowClassified 952 := by
  intro p generated legal
  have he : rowPose952 = p := Option.some.inj (row952_generated.symm.trans generated)
  subst p
  exact (row952_illegal legal).elim

def rowPose953 : Pose 7 := ⟨perm71, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row953_fields : pairFieldsMatchB 188160 facet0 facet833 key0 key953 rowPose953 = true := by decide +kernel
theorem row953_generated : rootPair 953 = some rowPose953 :=
  pairFieldsMatchB_sound (by decide) row953_fields
theorem row953_source : sourceKey 953 ∈ geometry.profile (sourceOwner 953) := by decide +kernel
theorem row953_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 833 key1).FastValid geometry rowPose953 := by decide +kernel
theorem row953_illegal : ¬ geometry.LegalContact rowPose953 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row953_reject_checked)
theorem row953_classified : RowClassified 953 := by
  intro p generated legal
  have he : rowPose953 = p := Option.some.inj (row953_generated.symm.trans generated)
  subst p
  exact (row953_illegal legal).elim

def rowPose954 : Pose 7 := ⟨perm95, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row954_fields : pairFieldsMatchB 188160 facet0 facet834 key0 key954 rowPose954 = true := by decide +kernel
theorem row954_generated : rootPair 954 = some rowPose954 :=
  pairFieldsMatchB_sound (by decide) row954_fields
theorem row954_source : sourceKey 954 ∈ geometry.profile (sourceOwner 954) := by decide +kernel
theorem row954_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 834 key0).FastValid geometry rowPose954 := by decide +kernel
theorem row954_illegal : ¬ geometry.LegalContact rowPose954 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row954_reject_checked)
theorem row954_classified : RowClassified 954 := by
  intro p generated legal
  have he : rowPose954 = p := Option.some.inj (row954_generated.symm.trans generated)
  subst p
  exact (row954_illegal legal).elim

def rowPose955 : Pose 7 := ⟨perm111, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row955_fields : pairFieldsMatchB 188160 facet0 facet835 key0 key955 rowPose955 = true := by decide +kernel
theorem row955_generated : rootPair 955 = some rowPose955 :=
  pairFieldsMatchB_sound (by decide) row955_fields
theorem row955_source : sourceKey 955 ∈ geometry.profile (sourceOwner 955) := by decide +kernel
theorem row955_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 835 key1).FastValid geometry rowPose955 := by decide +kernel
theorem row955_illegal : ¬ geometry.LegalContact rowPose955 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row955_reject_checked)
theorem row955_classified : RowClassified 955 := by
  intro p generated legal
  have he : rowPose955 = p := Option.some.inj (row955_generated.symm.trans generated)
  subst p
  exact (row955_illegal legal).elim

def rowPose956 : Pose 7 := ⟨perm5, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row956_fields : pairFieldsMatchB 188160 facet0 facet836 key0 key956 rowPose956 = true := by decide +kernel
theorem row956_generated : rootPair 956 = some rowPose956 :=
  pairFieldsMatchB_sound (by decide) row956_fields
theorem row956_source : sourceKey 956 ∈ geometry.profile (sourceOwner 956) := by decide +kernel
theorem row956_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 836 key1).FastValid geometry rowPose956 := by decide +kernel
theorem row956_illegal : ¬ geometry.LegalContact rowPose956 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row956_reject_checked)
theorem row956_classified : RowClassified 956 := by
  intro p generated legal
  have he : rowPose956 = p := Option.some.inj (row956_generated.symm.trans generated)
  subst p
  exact (row956_illegal legal).elim

def rowPose957 : Pose 7 := ⟨perm21, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row957_fields : pairFieldsMatchB 188160 facet0 facet837 key0 key957 rowPose957 = true := by decide +kernel
theorem row957_generated : rootPair 957 = some rowPose957 :=
  pairFieldsMatchB_sound (by decide) row957_fields
theorem row957_source : sourceKey 957 ∈ geometry.profile (sourceOwner 957) := by decide +kernel
theorem row957_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 837 key0).FastValid geometry rowPose957 := by decide +kernel
theorem row957_illegal : ¬ geometry.LegalContact rowPose957 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row957_reject_checked)
theorem row957_classified : RowClassified 957 := by
  intro p generated legal
  have he : rowPose957 = p := Option.some.inj (row957_generated.symm.trans generated)
  subst p
  exact (row957_illegal legal).elim

def rowPose958 : Pose 7 := ⟨perm42, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row958_fields : pairFieldsMatchB 188160 facet0 facet838 key0 key958 rowPose958 = true := by decide +kernel
theorem row958_generated : rootPair 958 = some rowPose958 :=
  pairFieldsMatchB_sound (by decide) row958_fields
theorem row958_source : sourceKey 958 ∈ geometry.profile (sourceOwner 958) := by decide +kernel
theorem row958_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 838 key0).FastValid geometry rowPose958 := by decide +kernel
theorem row958_illegal : ¬ geometry.LegalContact rowPose958 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row958_reject_checked)
theorem row958_classified : RowClassified 958 := by
  intro p generated legal
  have he : rowPose958 = p := Option.some.inj (row958_generated.symm.trans generated)
  subst p
  exact (row958_illegal legal).elim

def rowPose959 : Pose 7 := ⟨perm53, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row959_fields : pairFieldsMatchB 188160 facet0 facet839 key0 key959 rowPose959 = true := by decide +kernel
theorem row959_generated : rootPair 959 = some rowPose959 :=
  pairFieldsMatchB_sound (by decide) row959_fields
theorem row959_source : sourceKey 959 ∈ geometry.profile (sourceOwner 959) := by decide +kernel
theorem row959_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 811 key8).FastValid geometry rowPose959 := by decide +kernel
theorem row959_illegal : ¬ geometry.LegalContact rowPose959 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row959_reject_checked)
theorem row959_classified : RowClassified 959 := by
  intro p generated legal
  have he : rowPose959 = p := Option.some.inj (row959_generated.symm.trans generated)
  subst p
  exact (row959_illegal legal).elim

theorem chunk29_classified (i : Fin 32) : RowClassified ⟨928 + i.val, by omega⟩ := by
  fin_cases i
  · exact row928_classified
  · exact row929_classified
  · exact row930_classified
  · exact row931_classified
  · exact row932_classified
  · exact row933_classified
  · exact row934_classified
  · exact row935_classified
  · exact row936_classified
  · exact row937_classified
  · exact row938_classified
  · exact row939_classified
  · exact row940_classified
  · exact row941_classified
  · exact row942_classified
  · exact row943_classified
  · exact row944_classified
  · exact row945_classified
  · exact row946_classified
  · exact row947_classified
  · exact row948_classified
  · exact row949_classified
  · exact row950_classified
  · exact row951_classified
  · exact row952_classified
  · exact row953_classified
  · exact row954_classified
  · exact row955_classified
  · exact row956_classified
  · exact row957_classified
  · exact row958_classified
  · exact row959_classified

theorem chunk29_source (i : Fin 32) : sourceKey ⟨928 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨928 + i.val, by omega⟩) := by
  fin_cases i
  · exact row928_source
  · exact row929_source
  · exact row930_source
  · exact row931_source
  · exact row932_source
  · exact row933_source
  · exact row934_source
  · exact row935_source
  · exact row936_source
  · exact row937_source
  · exact row938_source
  · exact row939_source
  · exact row940_source
  · exact row941_source
  · exact row942_source
  · exact row943_source
  · exact row944_source
  · exact row945_source
  · exact row946_source
  · exact row947_source
  · exact row948_source
  · exact row949_source
  · exact row950_source
  · exact row951_source
  · exact row952_source
  · exact row953_source
  · exact row954_source
  · exact row955_source
  · exact row956_source
  · exact row957_source
  · exact row958_source
  · exact row959_source

#print axioms chunk29_classified
end SparseMonotiles.Contact.RootZeroPilot7
