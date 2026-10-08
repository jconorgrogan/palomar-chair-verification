module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose32 : Pose 7 := ⟨perm10, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row32_fields : pairFieldsMatchB 188160 facet0 facet28 key0 key32 rowPose32 = true := by decide +kernel
theorem row32_generated : rootPair 32 = some rowPose32 :=
  pairFieldsMatchB_sound (by decide) row32_fields
theorem row32_source : sourceKey 32 ∈ geometry.profile (sourceOwner 32) := by decide +kernel
theorem row32_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 28 key1).FastValid geometry rowPose32 := by decide +kernel
theorem row32_illegal : ¬ geometry.LegalContact rowPose32 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row32_reject_checked)
theorem row32_classified : RowClassified 32 := by
  intro p generated legal
  have he : rowPose32 = p := Option.some.inj (row32_generated.symm.trans generated)
  subst p
  exact (row32_illegal legal).elim

def rowPose33 : Pose 7 := ⟨perm22, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row33_fields : pairFieldsMatchB 188160 facet0 facet29 key0 key33 rowPose33 = true := by decide +kernel
theorem row33_generated : rootPair 33 = some rowPose33 :=
  pairFieldsMatchB_sound (by decide) row33_fields
theorem row33_source : sourceKey 33 ∈ geometry.profile (sourceOwner 33) := by decide +kernel
theorem row33_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 29 key0).FastValid geometry rowPose33 := by decide +kernel
theorem row33_illegal : ¬ geometry.LegalContact rowPose33 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row33_reject_checked)
theorem row33_classified : RowClassified 33 := by
  intro p generated legal
  have he : rowPose33 = p := Option.some.inj (row33_generated.symm.trans generated)
  subst p
  exact (row33_illegal legal).elim

def rowPose34 : Pose 7 := ⟨perm37, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row34_fields : pairFieldsMatchB 188160 facet0 facet30 key0 key34 rowPose34 = true := by decide +kernel
theorem row34_generated : rootPair 34 = some rowPose34 :=
  pairFieldsMatchB_sound (by decide) row34_fields
theorem row34_source : sourceKey 34 ∈ geometry.profile (sourceOwner 34) := by decide +kernel
theorem row34_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 30 key1).FastValid geometry rowPose34 := by decide +kernel
theorem row34_illegal : ¬ geometry.LegalContact rowPose34 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row34_reject_checked)
theorem row34_classified : RowClassified 34 := by
  intro p generated legal
  have he : rowPose34 = p := Option.some.inj (row34_generated.symm.trans generated)
  subst p
  exact (row34_illegal legal).elim

def rowPose35 : Pose 7 := ⟨perm58, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row35_fields : pairFieldsMatchB 188160 facet0 facet31 key0 key35 rowPose35 = true := by decide +kernel
theorem row35_generated : rootPair 35 = some rowPose35 :=
  pairFieldsMatchB_sound (by decide) row35_fields
theorem row35_source : sourceKey 35 ∈ geometry.profile (sourceOwner 35) := by decide +kernel
theorem row35_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 31 key1).FastValid geometry rowPose35 := by decide +kernel
theorem row35_illegal : ¬ geometry.LegalContact rowPose35 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row35_reject_checked)
theorem row35_classified : RowClassified 35 := by
  intro p generated legal
  have he : rowPose35 = p := Option.some.inj (row35_generated.symm.trans generated)
  subst p
  exact (row35_illegal legal).elim

def rowPose36 : Pose 7 := ⟨perm74, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row36_fields : pairFieldsMatchB 188160 facet0 facet32 key0 key36 rowPose36 = true := by decide +kernel
theorem row36_generated : rootPair 36 = some rowPose36 :=
  pairFieldsMatchB_sound (by decide) row36_fields
theorem row36_source : sourceKey 36 ∈ geometry.profile (sourceOwner 36) := by decide +kernel
theorem row36_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 88 key8).FastValid geometry rowPose36 := by decide +kernel
theorem row36_illegal : ¬ geometry.LegalContact rowPose36 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row36_reject_checked)
theorem row36_classified : RowClassified 36 := by
  intro p generated legal
  have he : rowPose36 = p := Option.some.inj (row36_generated.symm.trans generated)
  subst p
  exact (row36_illegal legal).elim

def rowPose37 : Pose 7 := ⟨perm69, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row37_fields : pairFieldsMatchB 188160 facet0 facet32 key0 key37 rowPose37 = true := by decide +kernel
theorem row37_generated : rootPair 37 = some rowPose37 :=
  pairFieldsMatchB_sound (by decide) row37_fields
theorem row37_source : sourceKey 37 ∈ geometry.profile (sourceOwner 37) := by decide +kernel
theorem row37_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 32 key0).FastValid geometry rowPose37 := by decide +kernel
theorem row37_illegal : ¬ geometry.LegalContact rowPose37 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row37_reject_checked)
theorem row37_classified : RowClassified 37 := by
  intro p generated legal
  have he : rowPose37 = p := Option.some.inj (row37_generated.symm.trans generated)
  subst p
  exact (row37_illegal legal).elim

def rowPose38 : Pose 7 := ⟨perm87, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row38_fields : pairFieldsMatchB 188160 facet0 facet33 key0 key38 rowPose38 = true := by decide +kernel
theorem row38_generated : rootPair 38 = some rowPose38 :=
  pairFieldsMatchB_sound (by decide) row38_fields
theorem row38_source : sourceKey 38 ∈ geometry.profile (sourceOwner 38) := by decide +kernel
theorem row38_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 33 key0).FastValid geometry rowPose38 := by decide +kernel
theorem row38_illegal : ¬ geometry.LegalContact rowPose38 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row38_reject_checked)
theorem row38_classified : RowClassified 38 := by
  intro p generated legal
  have he : rowPose38 = p := Option.some.inj (row38_generated.symm.trans generated)
  subst p
  exact (row38_illegal legal).elim

def rowPose39 : Pose 7 := ⟨perm96, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row39_fields : pairFieldsMatchB 188160 facet0 facet34 key0 key39 rowPose39 = true := by decide +kernel
theorem row39_generated : rootPair 39 = some rowPose39 :=
  pairFieldsMatchB_sound (by decide) row39_fields
theorem row39_source : sourceKey 39 ∈ geometry.profile (sourceOwner 39) := by decide +kernel
theorem row39_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 34 key0).FastValid geometry rowPose39 := by decide +kernel
theorem row39_illegal : ¬ geometry.LegalContact rowPose39 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row39_reject_checked)
theorem row39_classified : RowClassified 39 := by
  intro p generated legal
  have he : rowPose39 = p := Option.some.inj (row39_generated.symm.trans generated)
  subst p
  exact (row39_illegal legal).elim

def rowPose40 : Pose 7 := ⟨perm0, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row40_fields : pairFieldsMatchB 188160 facet0 facet35 key0 key40 rowPose40 = true := by decide +kernel
theorem row40_generated : rootPair 40 = some rowPose40 :=
  pairFieldsMatchB_sound (by decide) row40_fields
theorem row40_source : sourceKey 40 ∈ geometry.profile (sourceOwner 40) := by decide +kernel
theorem row40_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 35 key1).FastValid geometry rowPose40 := by decide +kernel
theorem row40_illegal : ¬ geometry.LegalContact rowPose40 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row40_reject_checked)
theorem row40_classified : RowClassified 40 := by
  intro p generated legal
  have he : rowPose40 = p := Option.some.inj (row40_generated.symm.trans generated)
  subst p
  exact (row40_illegal legal).elim

def rowPose41 : Pose 7 := ⟨perm16, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row41_fields : pairFieldsMatchB 188160 facet0 facet36 key0 key41 rowPose41 = true := by decide +kernel
theorem row41_generated : rootPair 41 = some rowPose41 :=
  pairFieldsMatchB_sound (by decide) row41_fields
theorem row41_source : sourceKey 41 ∈ geometry.profile (sourceOwner 41) := by decide +kernel
theorem row41_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 36 key0).FastValid geometry rowPose41 := by decide +kernel
theorem row41_illegal : ¬ geometry.LegalContact rowPose41 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row41_reject_checked)
theorem row41_classified : RowClassified 41 := by
  intro p generated legal
  have he : rowPose41 = p := Option.some.inj (row41_generated.symm.trans generated)
  subst p
  exact (row41_illegal legal).elim

def rowPose42 : Pose 7 := ⟨perm40, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row42_fields : pairFieldsMatchB 188160 facet0 facet37 key0 key42 rowPose42 = true := by decide +kernel
theorem row42_generated : rootPair 42 = some rowPose42 :=
  pairFieldsMatchB_sound (by decide) row42_fields
theorem row42_source : sourceKey 42 ∈ geometry.profile (sourceOwner 42) := by decide +kernel
theorem row42_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 37 key1).FastValid geometry rowPose42 := by decide +kernel
theorem row42_illegal : ¬ geometry.LegalContact rowPose42 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row42_reject_checked)
theorem row42_classified : RowClassified 42 := by
  intro p generated legal
  have he : rowPose42 = p := Option.some.inj (row42_generated.symm.trans generated)
  subst p
  exact (row42_illegal legal).elim

def rowPose43 : Pose 7 := ⟨perm53, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row43_fields : pairFieldsMatchB 188160 facet0 facet38 key0 key43 rowPose43 = true := by decide +kernel
theorem row43_generated : rootPair 43 = some rowPose43 :=
  pairFieldsMatchB_sound (by decide) row43_fields
theorem row43_source : sourceKey 43 ∈ geometry.profile (sourceOwner 43) := by decide +kernel
theorem row43_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 38 key0).FastValid geometry rowPose43 := by decide +kernel
theorem row43_illegal : ¬ geometry.LegalContact rowPose43 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row43_reject_checked)
theorem row43_classified : RowClassified 43 := by
  intro p generated legal
  have he : rowPose43 = p := Option.some.inj (row43_generated.symm.trans generated)
  subst p
  exact (row43_illegal legal).elim

def rowPose44 : Pose 7 := ⟨perm74, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row44_fields : pairFieldsMatchB 188160 facet0 facet39 key0 key44 rowPose44 = true := by decide +kernel
theorem row44_generated : rootPair 44 = some rowPose44 :=
  pairFieldsMatchB_sound (by decide) row44_fields
theorem row44_source : sourceKey 44 ∈ geometry.profile (sourceOwner 44) := by decide +kernel
theorem row44_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 39 key0).FastValid geometry rowPose44 := by decide +kernel
theorem row44_illegal : ¬ geometry.LegalContact rowPose44 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row44_reject_checked)
theorem row44_classified : RowClassified 44 := by
  intro p generated legal
  have he : rowPose44 = p := Option.some.inj (row44_generated.symm.trans generated)
  subst p
  exact (row44_illegal legal).elim

def rowPose45 : Pose 7 := ⟨perm90, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row45_fields : pairFieldsMatchB 188160 facet0 facet40 key0 key45 rowPose45 = true := by decide +kernel
theorem row45_generated : rootPair 45 = some rowPose45 :=
  pairFieldsMatchB_sound (by decide) row45_fields
theorem row45_source : sourceKey 45 ∈ geometry.profile (sourceOwner 45) := by decide +kernel
theorem row45_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 40 key0).FastValid geometry rowPose45 := by decide +kernel
theorem row45_illegal : ¬ geometry.LegalContact rowPose45 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row45_reject_checked)
theorem row45_classified : RowClassified 45 := by
  intro p generated legal
  have he : rowPose45 = p := Option.some.inj (row45_generated.symm.trans generated)
  subst p
  exact (row45_illegal legal).elim

def rowPose46 : Pose 7 := ⟨perm87, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row46_fields : pairFieldsMatchB 188160 facet0 facet40 key0 key46 rowPose46 = true := by decide +kernel
theorem row46_generated : rootPair 46 = some rowPose46 :=
  pairFieldsMatchB_sound (by decide) row46_fields
theorem row46_source : sourceKey 46 ∈ geometry.profile (sourceOwner 46) := by decide +kernel
theorem row46_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 33 key8).FastValid geometry rowPose46 := by decide +kernel
theorem row46_illegal : ¬ geometry.LegalContact rowPose46 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row46_reject_checked)
theorem row46_classified : RowClassified 46 := by
  intro p generated legal
  have he : rowPose46 = p := Option.some.inj (row46_generated.symm.trans generated)
  subst p
  exact (row46_illegal legal).elim

def rowPose47 : Pose 7 := ⟨perm111, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row47_fields : pairFieldsMatchB 188160 facet0 facet41 key0 key47 rowPose47 = true := by decide +kernel
theorem row47_generated : rootPair 47 = some rowPose47 :=
  pairFieldsMatchB_sound (by decide) row47_fields
theorem row47_source : sourceKey 47 ∈ geometry.profile (sourceOwner 47) := by decide +kernel
theorem row47_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 41 key1).FastValid geometry rowPose47 := by decide +kernel
theorem row47_illegal : ¬ geometry.LegalContact rowPose47 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row47_reject_checked)
theorem row47_classified : RowClassified 47 := by
  intro p generated legal
  have he : rowPose47 = p := Option.some.inj (row47_generated.symm.trans generated)
  subst p
  exact (row47_illegal legal).elim

def rowPose48 : Pose 7 := ⟨perm0, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row48_fields : pairFieldsMatchB 188160 facet0 facet42 key0 key48 rowPose48 = true := by decide +kernel
theorem row48_generated : rootPair 48 = some rowPose48 :=
  pairFieldsMatchB_sound (by decide) row48_fields
theorem row48_source : sourceKey 48 ∈ geometry.profile (sourceOwner 48) := by decide +kernel
theorem row48_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 42 key0).FastValid geometry rowPose48 := by decide +kernel
theorem row48_illegal : ¬ geometry.LegalContact rowPose48 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row48_reject_checked)
theorem row48_classified : RowClassified 48 := by
  intro p generated legal
  have he : rowPose48 = p := Option.some.inj (row48_generated.symm.trans generated)
  subst p
  exact (row48_illegal legal).elim

def rowPose49 : Pose 7 := ⟨perm21, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row49_fields : pairFieldsMatchB 188160 facet0 facet43 key0 key49 rowPose49 = true := by decide +kernel
theorem row49_generated : rootPair 49 = some rowPose49 :=
  pairFieldsMatchB_sound (by decide) row49_fields
theorem row49_source : sourceKey 49 ∈ geometry.profile (sourceOwner 49) := by decide +kernel
theorem row49_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 155 key8).FastValid geometry rowPose49 := by decide +kernel
theorem row49_illegal : ¬ geometry.LegalContact rowPose49 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row49_reject_checked)
theorem row49_classified : RowClassified 49 := by
  intro p generated legal
  have he : rowPose49 = p := Option.some.inj (row49_generated.symm.trans generated)
  subst p
  exact (row49_illegal legal).elim

def rowPose50 : Pose 7 := ⟨perm24, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row50_fields : pairFieldsMatchB 188160 facet0 facet43 key0 key50 rowPose50 = true := by decide +kernel
theorem row50_generated : rootPair 50 = some rowPose50 :=
  pairFieldsMatchB_sound (by decide) row50_fields
theorem row50_source : sourceKey 50 ∈ geometry.profile (sourceOwner 50) := by decide +kernel
theorem row50_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 43 key0).FastValid geometry rowPose50 := by decide +kernel
theorem row50_illegal : ¬ geometry.LegalContact rowPose50 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row50_reject_checked)
theorem row50_classified : RowClassified 50 := by
  intro p generated legal
  have he : rowPose50 = p := Option.some.inj (row50_generated.symm.trans generated)
  subst p
  exact (row50_illegal legal).elim

def rowPose51 : Pose 7 := ⟨perm37, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row51_fields : pairFieldsMatchB 188160 facet0 facet44 key0 key51 rowPose51 = true := by decide +kernel
theorem row51_generated : rootPair 51 = some rowPose51 :=
  pairFieldsMatchB_sound (by decide) row51_fields
theorem row51_source : sourceKey 51 ∈ geometry.profile (sourceOwner 51) := by decide +kernel
theorem row51_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 44 key1).FastValid geometry rowPose51 := by decide +kernel
theorem row51_illegal : ¬ geometry.LegalContact rowPose51 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row51_reject_checked)
theorem row51_classified : RowClassified 51 := by
  intro p generated legal
  have he : rowPose51 = p := Option.some.inj (row51_generated.symm.trans generated)
  subst p
  exact (row51_illegal legal).elim

def rowPose52 : Pose 7 := ⟨perm58, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row52_fields : pairFieldsMatchB 188160 facet0 facet45 key0 key52 rowPose52 = true := by decide +kernel
theorem row52_generated : rootPair 52 = some rowPose52 :=
  pairFieldsMatchB_sound (by decide) row52_fields
theorem row52_source : sourceKey 52 ∈ geometry.profile (sourceOwner 52) := by decide +kernel
theorem row52_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 45 key1).FastValid geometry rowPose52 := by decide +kernel
theorem row52_illegal : ¬ geometry.LegalContact rowPose52 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row52_reject_checked)
theorem row52_classified : RowClassified 52 := by
  intro p generated legal
  have he : rowPose52 = p := Option.some.inj (row52_generated.symm.trans generated)
  subst p
  exact (row52_illegal legal).elim

def rowPose53 : Pose 7 := ⟨perm71, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row53_fields : pairFieldsMatchB 188160 facet0 facet46 key0 key53 rowPose53 = true := by decide +kernel
theorem row53_generated : rootPair 53 = some rowPose53 :=
  pairFieldsMatchB_sound (by decide) row53_fields
theorem row53_source : sourceKey 53 ∈ geometry.profile (sourceOwner 53) := by decide +kernel
theorem row53_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 46 key0).FastValid geometry rowPose53 := by decide +kernel
theorem row53_illegal : ¬ geometry.LegalContact rowPose53 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row53_reject_checked)
theorem row53_classified : RowClassified 53 := by
  intro p generated legal
  have he : rowPose53 = p := Option.some.inj (row53_generated.symm.trans generated)
  subst p
  exact (row53_illegal legal).elim

def rowPose54 : Pose 7 := ⟨perm95, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row54_fields : pairFieldsMatchB 188160 facet0 facet47 key0 key54 rowPose54 = true := by decide +kernel
theorem row54_generated : rootPair 54 = some rowPose54 :=
  pairFieldsMatchB_sound (by decide) row54_fields
theorem row54_source : sourceKey 54 ∈ geometry.profile (sourceOwner 54) := by decide +kernel
theorem row54_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 47 key1).FastValid geometry rowPose54 := by decide +kernel
theorem row54_illegal : ¬ geometry.LegalContact rowPose54 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row54_reject_checked)
theorem row54_classified : RowClassified 54 := by
  intro p generated legal
  have he : rowPose54 = p := Option.some.inj (row54_generated.symm.trans generated)
  subst p
  exact (row54_illegal legal).elim

def rowPose55 : Pose 7 := ⟨perm111, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row55_fields : pairFieldsMatchB 188160 facet0 facet48 key0 key55 rowPose55 = true := by decide +kernel
theorem row55_generated : rootPair 55 = some rowPose55 :=
  pairFieldsMatchB_sound (by decide) row55_fields
theorem row55_source : sourceKey 55 ∈ geometry.profile (sourceOwner 55) := by decide +kernel
theorem row55_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 48 key0).FastValid geometry rowPose55 := by decide +kernel
theorem row55_illegal : ¬ geometry.LegalContact rowPose55 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row55_reject_checked)
theorem row55_classified : RowClassified 55 := by
  intro p generated legal
  have he : rowPose55 = p := Option.some.inj (row55_generated.symm.trans generated)
  subst p
  exact (row55_illegal legal).elim

def rowPose56 : Pose 7 := ⟨perm0, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row56_fields : pairFieldsMatchB 188160 facet0 facet49 key0 key56 rowPose56 = true := by decide +kernel
theorem row56_generated : rootPair 56 = some rowPose56 :=
  pairFieldsMatchB_sound (by decide) row56_fields
theorem row56_source : sourceKey 56 ∈ geometry.profile (sourceOwner 56) := by decide +kernel
theorem row56_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 49 key0).FastValid geometry rowPose56 := by decide +kernel
theorem row56_illegal : ¬ geometry.LegalContact rowPose56 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row56_reject_checked)
theorem row56_classified : RowClassified 56 := by
  intro p generated legal
  have he : rowPose56 = p := Option.some.inj (row56_generated.symm.trans generated)
  subst p
  exact (row56_illegal legal).elim

def rowPose57 : Pose 7 := ⟨perm16, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row57_fields : pairFieldsMatchB 188160 facet0 facet50 key0 key57 rowPose57 = true := by decide +kernel
theorem row57_generated : rootPair 57 = some rowPose57 :=
  pairFieldsMatchB_sound (by decide) row57_fields
theorem row57_source : sourceKey 57 ∈ geometry.profile (sourceOwner 57) := by decide +kernel
theorem row57_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 50 key1).FastValid geometry rowPose57 := by decide +kernel
theorem row57_illegal : ¬ geometry.LegalContact rowPose57 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row57_reject_checked)
theorem row57_classified : RowClassified 57 := by
  intro p generated legal
  have he : rowPose57 = p := Option.some.inj (row57_generated.symm.trans generated)
  subst p
  exact (row57_illegal legal).elim

def rowPose58 : Pose 7 := ⟨perm40, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row58_fields : pairFieldsMatchB 188160 facet0 facet51 key0 key58 rowPose58 = true := by decide +kernel
theorem row58_generated : rootPair 58 = some rowPose58 :=
  pairFieldsMatchB_sound (by decide) row58_fields
theorem row58_source : sourceKey 58 ∈ geometry.profile (sourceOwner 58) := by decide +kernel
theorem row58_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 51 key0).FastValid geometry rowPose58 := by decide +kernel
theorem row58_illegal : ¬ geometry.LegalContact rowPose58 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row58_reject_checked)
theorem row58_classified : RowClassified 58 := by
  intro p generated legal
  have he : rowPose58 = p := Option.some.inj (row58_generated.symm.trans generated)
  subst p
  exact (row58_illegal legal).elim

def rowPose59 : Pose 7 := ⟨perm53, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row59_fields : pairFieldsMatchB 188160 facet0 facet52 key0 key59 rowPose59 = true := by decide +kernel
theorem row59_generated : rootPair 59 = some rowPose59 :=
  pairFieldsMatchB_sound (by decide) row59_fields
theorem row59_source : sourceKey 59 ∈ geometry.profile (sourceOwner 59) := by decide +kernel
theorem row59_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 52 key1).FastValid geometry rowPose59 := by decide +kernel
theorem row59_illegal : ¬ geometry.LegalContact rowPose59 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row59_reject_checked)
theorem row59_classified : RowClassified 59 := by
  intro p generated legal
  have he : rowPose59 = p := Option.some.inj (row59_generated.symm.trans generated)
  subst p
  exact (row59_illegal legal).elim

def rowPose60 : Pose 7 := ⟨perm74, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row60_fields : pairFieldsMatchB 188160 facet0 facet53 key0 key60 rowPose60 = true := by decide +kernel
theorem row60_generated : rootPair 60 = some rowPose60 :=
  pairFieldsMatchB_sound (by decide) row60_fields
theorem row60_source : sourceKey 60 ∈ geometry.profile (sourceOwner 60) := by decide +kernel
theorem row60_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 53 key1).FastValid geometry rowPose60 := by decide +kernel
theorem row60_illegal : ¬ geometry.LegalContact rowPose60 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row60_reject_checked)
theorem row60_classified : RowClassified 60 := by
  intro p generated legal
  have he : rowPose60 = p := Option.some.inj (row60_generated.symm.trans generated)
  subst p
  exact (row60_illegal legal).elim

def rowPose61 : Pose 7 := ⟨perm90, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row61_fields : pairFieldsMatchB 188160 facet0 facet54 key0 key61 rowPose61 = true := by decide +kernel
theorem row61_generated : rootPair 61 = some rowPose61 :=
  pairFieldsMatchB_sound (by decide) row61_fields
theorem row61_source : sourceKey 61 ∈ geometry.profile (sourceOwner 61) := by decide +kernel
theorem row61_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 26 key8).FastValid geometry rowPose61 := by decide +kernel
theorem row61_illegal : ¬ geometry.LegalContact rowPose61 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row61_reject_checked)
theorem row61_classified : RowClassified 61 := by
  intro p generated legal
  have he : rowPose61 = p := Option.some.inj (row61_generated.symm.trans generated)
  subst p
  exact (row61_illegal legal).elim

def rowPose62 : Pose 7 := ⟨perm87, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row62_fields : pairFieldsMatchB 188160 facet0 facet54 key0 key62 rowPose62 = true := by decide +kernel
theorem row62_generated : rootPair 62 = some rowPose62 :=
  pairFieldsMatchB_sound (by decide) row62_fields
theorem row62_source : sourceKey 62 ∈ geometry.profile (sourceOwner 62) := by decide +kernel
theorem row62_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 54 key0).FastValid geometry rowPose62 := by decide +kernel
theorem row62_illegal : ¬ geometry.LegalContact rowPose62 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row62_reject_checked)
theorem row62_classified : RowClassified 62 := by
  intro p generated legal
  have he : rowPose62 = p := Option.some.inj (row62_generated.symm.trans generated)
  subst p
  exact (row62_illegal legal).elim

def rowPose63 : Pose 7 := ⟨perm111, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row63_fields : pairFieldsMatchB 188160 facet0 facet55 key0 key63 rowPose63 = true := by decide +kernel
theorem row63_generated : rootPair 63 = some rowPose63 :=
  pairFieldsMatchB_sound (by decide) row63_fields
theorem row63_source : sourceKey 63 ∈ geometry.profile (sourceOwner 63) := by decide +kernel
theorem row63_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 55 key0).FastValid geometry rowPose63 := by decide +kernel
theorem row63_illegal : ¬ geometry.LegalContact rowPose63 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row63_reject_checked)
theorem row63_classified : RowClassified 63 := by
  intro p generated legal
  have he : rowPose63 = p := Option.some.inj (row63_generated.symm.trans generated)
  subst p
  exact (row63_illegal legal).elim

theorem chunk01_classified (i : Fin 32) : RowClassified ⟨32 + i.val, by omega⟩ := by
  fin_cases i
  · exact row32_classified
  · exact row33_classified
  · exact row34_classified
  · exact row35_classified
  · exact row36_classified
  · exact row37_classified
  · exact row38_classified
  · exact row39_classified
  · exact row40_classified
  · exact row41_classified
  · exact row42_classified
  · exact row43_classified
  · exact row44_classified
  · exact row45_classified
  · exact row46_classified
  · exact row47_classified
  · exact row48_classified
  · exact row49_classified
  · exact row50_classified
  · exact row51_classified
  · exact row52_classified
  · exact row53_classified
  · exact row54_classified
  · exact row55_classified
  · exact row56_classified
  · exact row57_classified
  · exact row58_classified
  · exact row59_classified
  · exact row60_classified
  · exact row61_classified
  · exact row62_classified
  · exact row63_classified

theorem chunk01_source (i : Fin 32) : sourceKey ⟨32 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨32 + i.val, by omega⟩) := by
  fin_cases i
  · exact row32_source
  · exact row33_source
  · exact row34_source
  · exact row35_source
  · exact row36_source
  · exact row37_source
  · exact row38_source
  · exact row39_source
  · exact row40_source
  · exact row41_source
  · exact row42_source
  · exact row43_source
  · exact row44_source
  · exact row45_source
  · exact row46_source
  · exact row47_source
  · exact row48_source
  · exact row49_source
  · exact row50_source
  · exact row51_source
  · exact row52_source
  · exact row53_source
  · exact row54_source
  · exact row55_source
  · exact row56_source
  · exact row57_source
  · exact row58_source
  · exact row59_source
  · exact row60_source
  · exact row61_source
  · exact row62_source
  · exact row63_source

#print axioms chunk01_classified
end SparseMonotiles.Contact.RootZeroPilot7
