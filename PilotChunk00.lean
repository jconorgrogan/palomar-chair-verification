module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose0 : Pose 7 := ⟨perm0, ![true, false, false, false, false, false, false], ![0, 0, 0, 0, 0, 0, 0]⟩
theorem row0_fields : pairFieldsMatchB 188160 facet0 facet0 key0 key0 rowPose0 = true := by decide +kernel
theorem row0_generated : rootPair 0 = some rowPose0 :=
  pairFieldsMatchB_sound (by decide) row0_fields
theorem row0_source : sourceKey 0 ∈ geometry.profile (sourceOwner 0) := by decide +kernel
theorem row0_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 0 key0).FastValid geometry rowPose0 := by decide +kernel
theorem row0_illegal : ¬ geometry.LegalContact rowPose0 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row0_reject_checked)
theorem row0_classified : RowClassified 0 := by
  intro p generated legal
  have he : rowPose0 = p := Option.some.inj (row0_generated.symm.trans generated)
  subst p
  exact (row0_illegal legal).elim

def rowPose1 : Pose 7 := ⟨perm15, ![true, false, false, false, false, false, false], ![0, 0, 0, 0, 0, 0, 0]⟩
theorem row1_fields : pairFieldsMatchB 188160 facet0 facet0 key0 key1 rowPose1 = true := by decide +kernel
theorem row1_generated : rootPair 1 = some rowPose1 :=
  pairFieldsMatchB_sound (by decide) row1_fields
theorem row1_source : sourceKey 1 ∈ geometry.profile (sourceOwner 1) := by decide +kernel
theorem row1_catalog : rowPose1 ∈ M7 := by
  change rowPose1 ∈ Catalog7.supplied
  have he : rowPose1 = Catalog7.supplied.get ⟨214, by decide⟩ :=
    Pose.eq_of_sameCoordinates (by decide +kernel)
  rw [he]
  exact List.get_mem _ _
theorem row1_classified : RowClassified 1 := by
  intro p generated legal
  have he : rowPose1 = p := Option.some.inj (row1_generated.symm.trans generated)
  subst p
  exact row1_catalog

def rowPose2 : Pose 7 := ⟨perm21, ![true, true, false, false, true, true, true], ![0, 1, 0, 0, 1, 1, 1]⟩
theorem row2_fields : pairFieldsMatchB 188160 facet0 facet1 key0 key2 rowPose2 = true := by decide +kernel
theorem row2_generated : rootPair 2 = some rowPose2 :=
  pairFieldsMatchB_sound (by decide) row2_fields
theorem row2_source : sourceKey 2 ∈ geometry.profile (sourceOwner 2) := by decide +kernel
theorem row2_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 1 key1).FastValid geometry rowPose2 := by decide +kernel
theorem row2_illegal : ¬ geometry.LegalContact rowPose2 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row2_reject_checked)
theorem row2_classified : RowClassified 2 := by
  intro p generated legal
  have he : rowPose2 = p := Option.some.inj (row2_generated.symm.trans generated)
  subst p
  exact (row2_illegal legal).elim

def rowPose3 : Pose 7 := ⟨perm42, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, 0, 1, 1]⟩
theorem row3_fields : pairFieldsMatchB 188160 facet0 facet2 key0 key3 rowPose3 = true := by decide +kernel
theorem row3_generated : rootPair 3 = some rowPose3 :=
  pairFieldsMatchB_sound (by decide) row3_fields
theorem row3_source : sourceKey 3 ∈ geometry.profile (sourceOwner 3) := by decide +kernel
theorem row3_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 2 key1).FastValid geometry rowPose3 := by decide +kernel
theorem row3_illegal : ¬ geometry.LegalContact rowPose3 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row3_reject_checked)
theorem row3_classified : RowClassified 3 := by
  intro p generated legal
  have he : rowPose3 = p := Option.some.inj (row3_generated.symm.trans generated)
  subst p
  exact (row3_illegal legal).elim

def rowPose4 : Pose 7 := ⟨perm55, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 1, 0, 0]⟩
theorem row4_fields : pairFieldsMatchB 188160 facet0 facet3 key0 key4 rowPose4 = true := by decide +kernel
theorem row4_generated : rootPair 4 = some rowPose4 :=
  pairFieldsMatchB_sound (by decide) row4_fields
theorem row4_source : sourceKey 4 ∈ geometry.profile (sourceOwner 4) := by decide +kernel
theorem row4_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 3 key0).FastValid geometry rowPose4 := by decide +kernel
theorem row4_illegal : ¬ geometry.LegalContact rowPose4 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row4_reject_checked)
theorem row4_classified : RowClassified 4 := by
  intro p generated legal
  have he : rowPose4 = p := Option.some.inj (row4_generated.symm.trans generated)
  subst p
  exact (row4_illegal legal).elim

def rowPose5 : Pose 7 := ⟨perm73, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 1, 0, 0]⟩
theorem row5_fields : pairFieldsMatchB 188160 facet0 facet4 key0 key5 rowPose5 = true := by decide +kernel
theorem row5_generated : rootPair 5 = some rowPose5 :=
  pairFieldsMatchB_sound (by decide) row5_fields
theorem row5_source : sourceKey 5 ∈ geometry.profile (sourceOwner 5) := by decide +kernel
theorem row5_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 4 key1).FastValid geometry rowPose5 := by decide +kernel
theorem row5_illegal : ¬ geometry.LegalContact rowPose5 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row5_reject_checked)
theorem row5_classified : RowClassified 5 := by
  intro p generated legal
  have he : rowPose5 = p := Option.some.inj (row5_generated.symm.trans generated)
  subst p
  exact (row5_illegal legal).elim

def rowPose6 : Pose 7 := ⟨perm87, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, 0, 1, 1]⟩
theorem row6_fields : pairFieldsMatchB 188160 facet0 facet5 key0 key6 rowPose6 = true := by decide +kernel
theorem row6_generated : rootPair 6 = some rowPose6 :=
  pairFieldsMatchB_sound (by decide) row6_fields
theorem row6_source : sourceKey 6 ∈ geometry.profile (sourceOwner 6) := by decide +kernel
theorem row6_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 5 key0).FastValid geometry rowPose6 := by decide +kernel
theorem row6_illegal : ¬ geometry.LegalContact rowPose6 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row6_reject_checked)
theorem row6_classified : RowClassified 6 := by
  intro p generated legal
  have he : rowPose6 = p := Option.some.inj (row6_generated.symm.trans generated)
  subst p
  exact (row6_illegal legal).elim

def rowPose7 : Pose 7 := ⟨perm96, ![true, true, false, false, true, true, true], ![0, 1, 0, 0, 1, 1, 1]⟩
theorem row7_fields : pairFieldsMatchB 188160 facet0 facet6 key0 key7 rowPose7 = true := by decide +kernel
theorem row7_generated : rootPair 7 = some rowPose7 :=
  pairFieldsMatchB_sound (by decide) row7_fields
theorem row7_source : sourceKey 7 ∈ geometry.profile (sourceOwner 7) := by decide +kernel
theorem row7_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 6 key0).FastValid geometry rowPose7 := by decide +kernel
theorem row7_illegal : ¬ geometry.LegalContact rowPose7 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row7_reject_checked)
theorem row7_classified : RowClassified 7 := by
  intro p generated legal
  have he : rowPose7 = p := Option.some.inj (row7_generated.symm.trans generated)
  subst p
  exact (row7_illegal legal).elim

def rowPose8 : Pose 7 := ⟨perm15, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row8_fields : pairFieldsMatchB 188160 facet0 facet7 key0 key8 rowPose8 = true := by decide +kernel
theorem row8_generated : rootPair 8 = some rowPose8 :=
  pairFieldsMatchB_sound (by decide) row8_fields
theorem row8_source : sourceKey 8 ∈ geometry.profile (sourceOwner 8) := by decide +kernel
theorem row8_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 7 key0).FastValid geometry rowPose8 := by decide +kernel
theorem row8_illegal : ¬ geometry.LegalContact rowPose8 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row8_reject_checked)
theorem row8_classified : RowClassified 8 := by
  intro p generated legal
  have he : rowPose8 = p := Option.some.inj (row8_generated.symm.trans generated)
  subst p
  exact (row8_illegal legal).elim

def rowPose9 : Pose 7 := ⟨perm24, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row9_fields : pairFieldsMatchB 188160 facet0 facet8 key0 key9 rowPose9 = true := by decide +kernel
theorem row9_generated : rootPair 9 = some rowPose9 :=
  pairFieldsMatchB_sound (by decide) row9_fields
theorem row9_source : sourceKey 9 ∈ geometry.profile (sourceOwner 9) := by decide +kernel
theorem row9_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 8 key0).FastValid geometry rowPose9 := by decide +kernel
theorem row9_illegal : ¬ geometry.LegalContact rowPose9 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row9_reject_checked)
theorem row9_classified : RowClassified 9 := by
  intro p generated legal
  have he : rowPose9 = p := Option.some.inj (row9_generated.symm.trans generated)
  subst p
  exact (row9_illegal legal).elim

def rowPose10 : Pose 7 := ⟨perm38, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row10_fields : pairFieldsMatchB 188160 facet0 facet9 key0 key10 rowPose10 = true := by decide +kernel
theorem row10_generated : rootPair 10 = some rowPose10 :=
  pairFieldsMatchB_sound (by decide) row10_fields
theorem row10_source : sourceKey 10 ∈ geometry.profile (sourceOwner 10) := by decide +kernel
theorem row10_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 9 key1).FastValid geometry rowPose10 := by decide +kernel
theorem row10_illegal : ¬ geometry.LegalContact rowPose10 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row10_reject_checked)
theorem row10_classified : RowClassified 10 := by
  intro p generated legal
  have he : rowPose10 = p := Option.some.inj (row10_generated.symm.trans generated)
  subst p
  exact (row10_illegal legal).elim

def rowPose11 : Pose 7 := ⟨perm56, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row11_fields : pairFieldsMatchB 188160 facet0 facet10 key0 key11 rowPose11 = true := by decide +kernel
theorem row11_generated : rootPair 11 = some rowPose11 :=
  pairFieldsMatchB_sound (by decide) row11_fields
theorem row11_source : sourceKey 11 ∈ geometry.profile (sourceOwner 11) := by decide +kernel
theorem row11_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 10 key0).FastValid geometry rowPose11 := by decide +kernel
theorem row11_illegal : ¬ geometry.LegalContact rowPose11 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row11_reject_checked)
theorem row11_classified : RowClassified 11 := by
  intro p generated legal
  have he : rowPose11 = p := Option.some.inj (row11_generated.symm.trans generated)
  subst p
  exact (row11_illegal legal).elim

def rowPose12 : Pose 7 := ⟨perm69, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row12_fields : pairFieldsMatchB 188160 facet0 facet11 key0 key12 rowPose12 = true := by decide +kernel
theorem row12_generated : rootPair 12 = some rowPose12 :=
  pairFieldsMatchB_sound (by decide) row12_fields
theorem row12_source : sourceKey 12 ∈ geometry.profile (sourceOwner 12) := by decide +kernel
theorem row12_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 11 key1).FastValid geometry rowPose12 := by decide +kernel
theorem row12_illegal : ¬ geometry.LegalContact rowPose12 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row12_reject_checked)
theorem row12_classified : RowClassified 12 := by
  intro p generated legal
  have he : rowPose12 = p := Option.some.inj (row12_generated.symm.trans generated)
  subst p
  exact (row12_illegal legal).elim

def rowPose13 : Pose 7 := ⟨perm90, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row13_fields : pairFieldsMatchB 188160 facet0 facet12 key0 key13 rowPose13 = true := by decide +kernel
theorem row13_generated : rootPair 13 = some rowPose13 :=
  pairFieldsMatchB_sound (by decide) row13_fields
theorem row13_source : sourceKey 13 ∈ geometry.profile (sourceOwner 13) := by decide +kernel
theorem row13_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 12 key1).FastValid geometry rowPose13 := by decide +kernel
theorem row13_illegal : ¬ geometry.LegalContact rowPose13 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row13_reject_checked)
theorem row13_classified : RowClassified 13 := by
  intro p generated legal
  have he : rowPose13 = p := Option.some.inj (row13_generated.symm.trans generated)
  subst p
  exact (row13_illegal legal).elim

def rowPose14 : Pose 7 := ⟨perm96, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row14_fields : pairFieldsMatchB 188160 facet0 facet13 key0 key14 rowPose14 = true := by decide +kernel
theorem row14_generated : rootPair 14 = some rowPose14 :=
  pairFieldsMatchB_sound (by decide) row14_fields
theorem row14_source : sourceKey 14 ∈ geometry.profile (sourceOwner 14) := by decide +kernel
theorem row14_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 27 key8).FastValid geometry rowPose14 := by decide +kernel
theorem row14_illegal : ¬ geometry.LegalContact rowPose14 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row14_reject_checked)
theorem row14_classified : RowClassified 14 := by
  intro p generated legal
  have he : rowPose14 = p := Option.some.inj (row14_generated.symm.trans generated)
  subst p
  exact (row14_illegal legal).elim

def rowPose15 : Pose 7 := ⟨perm111, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row15_fields : pairFieldsMatchB 188160 facet0 facet13 key0 key15 rowPose15 = true := by decide +kernel
theorem row15_generated : rootPair 15 = some rowPose15 :=
  pairFieldsMatchB_sound (by decide) row15_fields
theorem row15_source : sourceKey 15 ∈ geometry.profile (sourceOwner 15) := by decide +kernel
theorem row15_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 13 key0).FastValid geometry rowPose15 := by decide +kernel
theorem row15_illegal : ¬ geometry.LegalContact rowPose15 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row15_reject_checked)
theorem row15_classified : RowClassified 15 := by
  intro p generated legal
  have he : rowPose15 = p := Option.some.inj (row15_generated.symm.trans generated)
  subst p
  exact (row15_illegal legal).elim

def rowPose16 : Pose 7 := ⟨perm0, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row16_fields : pairFieldsMatchB 188160 facet0 facet14 key0 key16 rowPose16 = true := by decide +kernel
theorem row16_generated : rootPair 16 = some rowPose16 :=
  pairFieldsMatchB_sound (by decide) row16_fields
theorem row16_source : sourceKey 16 ∈ geometry.profile (sourceOwner 16) := by decide +kernel
theorem row16_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 14 key0).FastValid geometry rowPose16 := by decide +kernel
theorem row16_illegal : ¬ geometry.LegalContact rowPose16 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row16_reject_checked)
theorem row16_classified : RowClassified 16 := by
  intro p generated legal
  have he : rowPose16 = p := Option.some.inj (row16_generated.symm.trans generated)
  subst p
  exact (row16_illegal legal).elim

def rowPose17 : Pose 7 := ⟨perm16, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row17_fields : pairFieldsMatchB 188160 facet0 facet15 key0 key17 rowPose17 = true := by decide +kernel
theorem row17_generated : rootPair 17 = some rowPose17 :=
  pairFieldsMatchB_sound (by decide) row17_fields
theorem row17_source : sourceKey 17 ∈ geometry.profile (sourceOwner 17) := by decide +kernel
theorem row17_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 15 key1).FastValid geometry rowPose17 := by decide +kernel
theorem row17_illegal : ¬ geometry.LegalContact rowPose17 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row17_reject_checked)
theorem row17_classified : RowClassified 17 := by
  intro p generated legal
  have he : rowPose17 = p := Option.some.inj (row17_generated.symm.trans generated)
  subst p
  exact (row17_illegal legal).elim

def rowPose18 : Pose 7 := ⟨perm40, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row18_fields : pairFieldsMatchB 188160 facet0 facet16 key0 key18 rowPose18 = true := by decide +kernel
theorem row18_generated : rootPair 18 = some rowPose18 :=
  pairFieldsMatchB_sound (by decide) row18_fields
theorem row18_source : sourceKey 18 ∈ geometry.profile (sourceOwner 18) := by decide +kernel
theorem row18_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 16 key0).FastValid geometry rowPose18 := by decide +kernel
theorem row18_illegal : ¬ geometry.LegalContact rowPose18 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row18_reject_checked)
theorem row18_classified : RowClassified 18 := by
  intro p generated legal
  have he : rowPose18 = p := Option.some.inj (row18_generated.symm.trans generated)
  subst p
  exact (row18_illegal legal).elim

def rowPose19 : Pose 7 := ⟨perm53, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row19_fields : pairFieldsMatchB 188160 facet0 facet17 key0 key19 rowPose19 = true := by decide +kernel
theorem row19_generated : rootPair 19 = some rowPose19 :=
  pairFieldsMatchB_sound (by decide) row19_fields
theorem row19_source : sourceKey 19 ∈ geometry.profile (sourceOwner 19) := by decide +kernel
theorem row19_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 17 key1).FastValid geometry rowPose19 := by decide +kernel
theorem row19_illegal : ¬ geometry.LegalContact rowPose19 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row19_reject_checked)
theorem row19_classified : RowClassified 19 := by
  intro p generated legal
  have he : rowPose19 = p := Option.some.inj (row19_generated.symm.trans generated)
  subst p
  exact (row19_illegal legal).elim

def rowPose20 : Pose 7 := ⟨perm74, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row20_fields : pairFieldsMatchB 188160 facet0 facet18 key0 key20 rowPose20 = true := by decide +kernel
theorem row20_generated : rootPair 20 = some rowPose20 :=
  pairFieldsMatchB_sound (by decide) row20_fields
theorem row20_source : sourceKey 20 ∈ geometry.profile (sourceOwner 20) := by decide +kernel
theorem row20_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 18 key1).FastValid geometry rowPose20 := by decide +kernel
theorem row20_illegal : ¬ geometry.LegalContact rowPose20 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row20_reject_checked)
theorem row20_classified : RowClassified 20 := by
  intro p generated legal
  have he : rowPose20 = p := Option.some.inj (row20_generated.symm.trans generated)
  subst p
  exact (row20_illegal legal).elim

def rowPose21 : Pose 7 := ⟨perm90, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row21_fields : pairFieldsMatchB 188160 facet0 facet19 key0 key21 rowPose21 = true := by decide +kernel
theorem row21_generated : rootPair 21 = some rowPose21 :=
  pairFieldsMatchB_sound (by decide) row21_fields
theorem row21_source : sourceKey 21 ∈ geometry.profile (sourceOwner 21) := by decide +kernel
theorem row21_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 47 key8).FastValid geometry rowPose21 := by decide +kernel
theorem row21_illegal : ¬ geometry.LegalContact rowPose21 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row21_reject_checked)
theorem row21_classified : RowClassified 21 := by
  intro p generated legal
  have he : rowPose21 = p := Option.some.inj (row21_generated.symm.trans generated)
  subst p
  exact (row21_illegal legal).elim

def rowPose22 : Pose 7 := ⟨perm87, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row22_fields : pairFieldsMatchB 188160 facet0 facet19 key0 key22 rowPose22 = true := by decide +kernel
theorem row22_generated : rootPair 22 = some rowPose22 :=
  pairFieldsMatchB_sound (by decide) row22_fields
theorem row22_source : sourceKey 22 ∈ geometry.profile (sourceOwner 22) := by decide +kernel
theorem row22_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 19 key0).FastValid geometry rowPose22 := by decide +kernel
theorem row22_illegal : ¬ geometry.LegalContact rowPose22 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row22_reject_checked)
theorem row22_classified : RowClassified 22 := by
  intro p generated legal
  have he : rowPose22 = p := Option.some.inj (row22_generated.symm.trans generated)
  subst p
  exact (row22_illegal legal).elim

def rowPose23 : Pose 7 := ⟨perm111, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row23_fields : pairFieldsMatchB 188160 facet0 facet20 key0 key23 rowPose23 = true := by decide +kernel
theorem row23_generated : rootPair 23 = some rowPose23 :=
  pairFieldsMatchB_sound (by decide) row23_fields
theorem row23_source : sourceKey 23 ∈ geometry.profile (sourceOwner 23) := by decide +kernel
theorem row23_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 20 key0).FastValid geometry rowPose23 := by decide +kernel
theorem row23_illegal : ¬ geometry.LegalContact rowPose23 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row23_reject_checked)
theorem row23_classified : RowClassified 23 := by
  intro p generated legal
  have he : rowPose23 = p := Option.some.inj (row23_generated.symm.trans generated)
  subst p
  exact (row23_illegal legal).elim

def rowPose24 : Pose 7 := ⟨perm15, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row24_fields : pairFieldsMatchB 188160 facet0 facet21 key0 key24 rowPose24 = true := by decide +kernel
theorem row24_generated : rootPair 24 = some rowPose24 :=
  pairFieldsMatchB_sound (by decide) row24_fields
theorem row24_source : sourceKey 24 ∈ geometry.profile (sourceOwner 24) := by decide +kernel
theorem row24_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 21 key0).FastValid geometry rowPose24 := by decide +kernel
theorem row24_illegal : ¬ geometry.LegalContact rowPose24 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row24_reject_checked)
theorem row24_classified : RowClassified 24 := by
  intro p generated legal
  have he : rowPose24 = p := Option.some.inj (row24_generated.symm.trans generated)
  subst p
  exact (row24_illegal legal).elim

def rowPose25 : Pose 7 := ⟨perm24, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row25_fields : pairFieldsMatchB 188160 facet0 facet22 key0 key25 rowPose25 = true := by decide +kernel
theorem row25_generated : rootPair 25 = some rowPose25 :=
  pairFieldsMatchB_sound (by decide) row25_fields
theorem row25_source : sourceKey 25 ∈ geometry.profile (sourceOwner 25) := by decide +kernel
theorem row25_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 22 key0).FastValid geometry rowPose25 := by decide +kernel
theorem row25_illegal : ¬ geometry.LegalContact rowPose25 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row25_reject_checked)
theorem row25_classified : RowClassified 25 := by
  intro p generated legal
  have he : rowPose25 = p := Option.some.inj (row25_generated.symm.trans generated)
  subst p
  exact (row25_illegal legal).elim

def rowPose26 : Pose 7 := ⟨perm37, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row26_fields : pairFieldsMatchB 188160 facet0 facet23 key0 key26 rowPose26 = true := by decide +kernel
theorem row26_generated : rootPair 26 = some rowPose26 :=
  pairFieldsMatchB_sound (by decide) row26_fields
theorem row26_source : sourceKey 26 ∈ geometry.profile (sourceOwner 26) := by decide +kernel
theorem row26_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 79 key8).FastValid geometry rowPose26 := by decide +kernel
theorem row26_illegal : ¬ geometry.LegalContact rowPose26 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row26_reject_checked)
theorem row26_classified : RowClassified 26 := by
  intro p generated legal
  have he : rowPose26 = p := Option.some.inj (row26_generated.symm.trans generated)
  subst p
  exact (row26_illegal legal).elim

def rowPose27 : Pose 7 := ⟨perm42, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row27_fields : pairFieldsMatchB 188160 facet0 facet23 key0 key27 rowPose27 = true := by decide +kernel
theorem row27_generated : rootPair 27 = some rowPose27 :=
  pairFieldsMatchB_sound (by decide) row27_fields
theorem row27_source : sourceKey 27 ∈ geometry.profile (sourceOwner 27) := by decide +kernel
theorem row27_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 23 key0).FastValid geometry rowPose27 := by decide +kernel
theorem row27_illegal : ¬ geometry.LegalContact rowPose27 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row27_reject_checked)
theorem row27_classified : RowClassified 27 := by
  intro p generated legal
  have he : rowPose27 = p := Option.some.inj (row27_generated.symm.trans generated)
  subst p
  exact (row27_illegal legal).elim

def rowPose28 : Pose 7 := ⟨perm53, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row28_fields : pairFieldsMatchB 188160 facet0 facet24 key0 key28 rowPose28 = true := by decide +kernel
theorem row28_generated : rootPair 28 = some rowPose28 :=
  pairFieldsMatchB_sound (by decide) row28_fields
theorem row28_source : sourceKey 28 ∈ geometry.profile (sourceOwner 28) := by decide +kernel
theorem row28_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 24 key1).FastValid geometry rowPose28 := by decide +kernel
theorem row28_illegal : ¬ geometry.LegalContact rowPose28 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row28_reject_checked)
theorem row28_classified : RowClassified 28 := by
  intro p generated legal
  have he : rowPose28 = p := Option.some.inj (row28_generated.symm.trans generated)
  subst p
  exact (row28_illegal legal).elim

def rowPose29 : Pose 7 := ⟨perm74, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row29_fields : pairFieldsMatchB 188160 facet0 facet25 key0 key29 rowPose29 = true := by decide +kernel
theorem row29_generated : rootPair 29 = some rowPose29 :=
  pairFieldsMatchB_sound (by decide) row29_fields
theorem row29_source : sourceKey 29 ∈ geometry.profile (sourceOwner 29) := by decide +kernel
theorem row29_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 25 key1).FastValid geometry rowPose29 := by decide +kernel
theorem row29_illegal : ¬ geometry.LegalContact rowPose29 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row29_reject_checked)
theorem row29_classified : RowClassified 29 := by
  intro p generated legal
  have he : rowPose29 = p := Option.some.inj (row29_generated.symm.trans generated)
  subst p
  exact (row29_illegal legal).elim

def rowPose30 : Pose 7 := ⟨perm89, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row30_fields : pairFieldsMatchB 188160 facet0 facet26 key0 key30 rowPose30 = true := by decide +kernel
theorem row30_generated : rootPair 30 = some rowPose30 :=
  pairFieldsMatchB_sound (by decide) row30_fields
theorem row30_source : sourceKey 30 ∈ geometry.profile (sourceOwner 30) := by decide +kernel
theorem row30_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 26 key0).FastValid geometry rowPose30 := by decide +kernel
theorem row30_illegal : ¬ geometry.LegalContact rowPose30 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row30_reject_checked)
theorem row30_classified : RowClassified 30 := by
  intro p generated legal
  have he : rowPose30 = p := Option.some.inj (row30_generated.symm.trans generated)
  subst p
  exact (row30_illegal legal).elim

def rowPose31 : Pose 7 := ⟨perm101, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row31_fields : pairFieldsMatchB 188160 facet0 facet27 key0 key31 rowPose31 = true := by decide +kernel
theorem row31_generated : rootPair 31 = some rowPose31 :=
  pairFieldsMatchB_sound (by decide) row31_fields
theorem row31_source : sourceKey 31 ∈ geometry.profile (sourceOwner 31) := by decide +kernel
theorem row31_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 27 key1).FastValid geometry rowPose31 := by decide +kernel
theorem row31_illegal : ¬ geometry.LegalContact rowPose31 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row31_reject_checked)
theorem row31_classified : RowClassified 31 := by
  intro p generated legal
  have he : rowPose31 = p := Option.some.inj (row31_generated.symm.trans generated)
  subst p
  exact (row31_illegal legal).elim

theorem chunk00_classified (i : Fin 32) : RowClassified ⟨0 + i.val, by omega⟩ := by
  fin_cases i
  · exact row0_classified
  · exact row1_classified
  · exact row2_classified
  · exact row3_classified
  · exact row4_classified
  · exact row5_classified
  · exact row6_classified
  · exact row7_classified
  · exact row8_classified
  · exact row9_classified
  · exact row10_classified
  · exact row11_classified
  · exact row12_classified
  · exact row13_classified
  · exact row14_classified
  · exact row15_classified
  · exact row16_classified
  · exact row17_classified
  · exact row18_classified
  · exact row19_classified
  · exact row20_classified
  · exact row21_classified
  · exact row22_classified
  · exact row23_classified
  · exact row24_classified
  · exact row25_classified
  · exact row26_classified
  · exact row27_classified
  · exact row28_classified
  · exact row29_classified
  · exact row30_classified
  · exact row31_classified

theorem chunk00_source (i : Fin 32) : sourceKey ⟨0 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨0 + i.val, by omega⟩) := by
  fin_cases i
  · exact row0_source
  · exact row1_source
  · exact row2_source
  · exact row3_source
  · exact row4_source
  · exact row5_source
  · exact row6_source
  · exact row7_source
  · exact row8_source
  · exact row9_source
  · exact row10_source
  · exact row11_source
  · exact row12_source
  · exact row13_source
  · exact row14_source
  · exact row15_source
  · exact row16_source
  · exact row17_source
  · exact row18_source
  · exact row19_source
  · exact row20_source
  · exact row21_source
  · exact row22_source
  · exact row23_source
  · exact row24_source
  · exact row25_source
  · exact row26_source
  · exact row27_source
  · exact row28_source
  · exact row29_source
  · exact row30_source
  · exact row31_source

#print axioms chunk00_classified
end SparseMonotiles.Contact.RootZeroPilot7
