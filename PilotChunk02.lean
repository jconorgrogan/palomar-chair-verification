module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose64 : Pose 7 := ⟨perm5, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row64_fields : pairFieldsMatchB 188160 facet0 facet56 key0 key64 rowPose64 = true := by decide +kernel
theorem row64_generated : rootPair 64 = some rowPose64 :=
  pairFieldsMatchB_sound (by decide) row64_fields
theorem row64_source : sourceKey 64 ∈ geometry.profile (sourceOwner 64) := by decide +kernel
theorem row64_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 56 key0).FastValid geometry rowPose64 := by decide +kernel
theorem row64_illegal : ¬ geometry.LegalContact rowPose64 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row64_reject_checked)
theorem row64_classified : RowClassified 64 := by
  intro p generated legal
  have he : rowPose64 = p := Option.some.inj (row64_generated.symm.trans generated)
  subst p
  exact (row64_illegal legal).elim

def rowPose65 : Pose 7 := ⟨perm21, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row65_fields : pairFieldsMatchB 188160 facet0 facet57 key0 key65 rowPose65 = true := by decide +kernel
theorem row65_generated : rootPair 65 = some rowPose65 :=
  pairFieldsMatchB_sound (by decide) row65_fields
theorem row65_source : sourceKey 65 ∈ geometry.profile (sourceOwner 65) := by decide +kernel
theorem row65_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 57 key1).FastValid geometry rowPose65 := by decide +kernel
theorem row65_illegal : ¬ geometry.LegalContact rowPose65 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row65_reject_checked)
theorem row65_classified : RowClassified 65 := by
  intro p generated legal
  have he : rowPose65 = p := Option.some.inj (row65_generated.symm.trans generated)
  subst p
  exact (row65_illegal legal).elim

def rowPose66 : Pose 7 := ⟨perm42, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row66_fields : pairFieldsMatchB 188160 facet0 facet58 key0 key66 rowPose66 = true := by decide +kernel
theorem row66_generated : rootPair 66 = some rowPose66 :=
  pairFieldsMatchB_sound (by decide) row66_fields
theorem row66_source : sourceKey 66 ∈ geometry.profile (sourceOwner 66) := by decide +kernel
theorem row66_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 58 key1).FastValid geometry rowPose66 := by decide +kernel
theorem row66_illegal : ¬ geometry.LegalContact rowPose66 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row66_reject_checked)
theorem row66_classified : RowClassified 66 := by
  intro p generated legal
  have he : rowPose66 = p := Option.some.inj (row66_generated.symm.trans generated)
  subst p
  exact (row66_illegal legal).elim

def rowPose67 : Pose 7 := ⟨perm53, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row67_fields : pairFieldsMatchB 188160 facet0 facet59 key0 key67 rowPose67 = true := by decide +kernel
theorem row67_generated : rootPair 67 = some rowPose67 :=
  pairFieldsMatchB_sound (by decide) row67_fields
theorem row67_source : sourceKey 67 ∈ geometry.profile (sourceOwner 67) := by decide +kernel
theorem row67_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 59 key0).FastValid geometry rowPose67 := by decide +kernel
theorem row67_illegal : ¬ geometry.LegalContact rowPose67 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row67_reject_checked)
theorem row67_classified : RowClassified 67 := by
  intro p generated legal
  have he : rowPose67 = p := Option.some.inj (row67_generated.symm.trans generated)
  subst p
  exact (row67_illegal legal).elim

def rowPose68 : Pose 7 := ⟨perm58, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row68_fields : pairFieldsMatchB 188160 facet0 facet59 key0 key68 rowPose68 = true := by decide +kernel
theorem row68_generated : rootPair 68 = some rowPose68 :=
  pairFieldsMatchB_sound (by decide) row68_fields
theorem row68_source : sourceKey 68 ∈ geometry.profile (sourceOwner 68) := by decide +kernel
theorem row68_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 171 key8).FastValid geometry rowPose68 := by decide +kernel
theorem row68_illegal : ¬ geometry.LegalContact rowPose68 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row68_reject_checked)
theorem row68_classified : RowClassified 68 := by
  intro p generated legal
  have he : rowPose68 = p := Option.some.inj (row68_generated.symm.trans generated)
  subst p
  exact (row68_illegal legal).elim

def rowPose69 : Pose 7 := ⟨perm69, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row69_fields : pairFieldsMatchB 188160 facet0 facet60 key0 key69 rowPose69 = true := by decide +kernel
theorem row69_generated : rootPair 69 = some rowPose69 :=
  pairFieldsMatchB_sound (by decide) row69_fields
theorem row69_source : sourceKey 69 ∈ geometry.profile (sourceOwner 69) := by decide +kernel
theorem row69_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 60 key0).FastValid geometry rowPose69 := by decide +kernel
theorem row69_illegal : ¬ geometry.LegalContact rowPose69 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row69_reject_checked)
theorem row69_classified : RowClassified 69 := by
  intro p generated legal
  have he : rowPose69 = p := Option.some.inj (row69_generated.symm.trans generated)
  subst p
  exact (row69_illegal legal).elim

def rowPose70 : Pose 7 := ⟨perm90, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row70_fields : pairFieldsMatchB 188160 facet0 facet61 key0 key70 rowPose70 = true := by decide +kernel
theorem row70_generated : rootPair 70 = some rowPose70 :=
  pairFieldsMatchB_sound (by decide) row70_fields
theorem row70_source : sourceKey 70 ∈ geometry.profile (sourceOwner 70) := by decide +kernel
theorem row70_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 61 key0).FastValid geometry rowPose70 := by decide +kernel
theorem row70_illegal : ¬ geometry.LegalContact rowPose70 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row70_reject_checked)
theorem row70_classified : RowClassified 70 := by
  intro p generated legal
  have he : rowPose70 = p := Option.some.inj (row70_generated.symm.trans generated)
  subst p
  exact (row70_illegal legal).elim

def rowPose71 : Pose 7 := ⟨perm106, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row71_fields : pairFieldsMatchB 188160 facet0 facet62 key0 key71 rowPose71 = true := by decide +kernel
theorem row71_generated : rootPair 71 = some rowPose71 :=
  pairFieldsMatchB_sound (by decide) row71_fields
theorem row71_source : sourceKey 71 ∈ geometry.profile (sourceOwner 71) := by decide +kernel
theorem row71_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 62 key1).FastValid geometry rowPose71 := by decide +kernel
theorem row71_illegal : ¬ geometry.LegalContact rowPose71 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row71_reject_checked)
theorem row71_classified : RowClassified 71 := by
  intro p generated legal
  have he : rowPose71 = p := Option.some.inj (row71_generated.symm.trans generated)
  subst p
  exact (row71_illegal legal).elim

def rowPose72 : Pose 7 := ⟨perm0, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row72_fields : pairFieldsMatchB 188160 facet0 facet63 key0 key72 rowPose72 = true := by decide +kernel
theorem row72_generated : rootPair 72 = some rowPose72 :=
  pairFieldsMatchB_sound (by decide) row72_fields
theorem row72_source : sourceKey 72 ∈ geometry.profile (sourceOwner 72) := by decide +kernel
theorem row72_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 63 key0).FastValid geometry rowPose72 := by decide +kernel
theorem row72_illegal : ¬ geometry.LegalContact rowPose72 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row72_reject_checked)
theorem row72_classified : RowClassified 72 := by
  intro p generated legal
  have he : rowPose72 = p := Option.some.inj (row72_generated.symm.trans generated)
  subst p
  exact (row72_illegal legal).elim

def rowPose73 : Pose 7 := ⟨perm21, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row73_fields : pairFieldsMatchB 188160 facet0 facet64 key0 key73 rowPose73 = true := by decide +kernel
theorem row73_generated : rootPair 73 = some rowPose73 :=
  pairFieldsMatchB_sound (by decide) row73_fields
theorem row73_source : sourceKey 73 ∈ geometry.profile (sourceOwner 73) := by decide +kernel
theorem row73_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 176 key8).FastValid geometry rowPose73 := by decide +kernel
theorem row73_illegal : ¬ geometry.LegalContact rowPose73 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row73_reject_checked)
theorem row73_classified : RowClassified 73 := by
  intro p generated legal
  have he : rowPose73 = p := Option.some.inj (row73_generated.symm.trans generated)
  subst p
  exact (row73_illegal legal).elim

def rowPose74 : Pose 7 := ⟨perm24, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row74_fields : pairFieldsMatchB 188160 facet0 facet64 key0 key74 rowPose74 = true := by decide +kernel
theorem row74_generated : rootPair 74 = some rowPose74 :=
  pairFieldsMatchB_sound (by decide) row74_fields
theorem row74_source : sourceKey 74 ∈ geometry.profile (sourceOwner 74) := by decide +kernel
theorem row74_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 64 key0).FastValid geometry rowPose74 := by decide +kernel
theorem row74_illegal : ¬ geometry.LegalContact rowPose74 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row74_reject_checked)
theorem row74_classified : RowClassified 74 := by
  intro p generated legal
  have he : rowPose74 = p := Option.some.inj (row74_generated.symm.trans generated)
  subst p
  exact (row74_illegal legal).elim

def rowPose75 : Pose 7 := ⟨perm37, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row75_fields : pairFieldsMatchB 188160 facet0 facet65 key0 key75 rowPose75 = true := by decide +kernel
theorem row75_generated : rootPair 75 = some rowPose75 :=
  pairFieldsMatchB_sound (by decide) row75_fields
theorem row75_source : sourceKey 75 ∈ geometry.profile (sourceOwner 75) := by decide +kernel
theorem row75_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 65 key1).FastValid geometry rowPose75 := by decide +kernel
theorem row75_illegal : ¬ geometry.LegalContact rowPose75 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row75_reject_checked)
theorem row75_classified : RowClassified 75 := by
  intro p generated legal
  have he : rowPose75 = p := Option.some.inj (row75_generated.symm.trans generated)
  subst p
  exact (row75_illegal legal).elim

def rowPose76 : Pose 7 := ⟨perm58, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row76_fields : pairFieldsMatchB 188160 facet0 facet66 key0 key76 rowPose76 = true := by decide +kernel
theorem row76_generated : rootPair 76 = some rowPose76 :=
  pairFieldsMatchB_sound (by decide) row76_fields
theorem row76_source : sourceKey 76 ∈ geometry.profile (sourceOwner 76) := by decide +kernel
theorem row76_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 66 key1).FastValid geometry rowPose76 := by decide +kernel
theorem row76_illegal : ¬ geometry.LegalContact rowPose76 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row76_reject_checked)
theorem row76_classified : RowClassified 76 := by
  intro p generated legal
  have he : rowPose76 = p := Option.some.inj (row76_generated.symm.trans generated)
  subst p
  exact (row76_illegal legal).elim

def rowPose77 : Pose 7 := ⟨perm71, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row77_fields : pairFieldsMatchB 188160 facet0 facet67 key0 key77 rowPose77 = true := by decide +kernel
theorem row77_generated : rootPair 77 = some rowPose77 :=
  pairFieldsMatchB_sound (by decide) row77_fields
theorem row77_source : sourceKey 77 ∈ geometry.profile (sourceOwner 77) := by decide +kernel
theorem row77_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 67 key0).FastValid geometry rowPose77 := by decide +kernel
theorem row77_illegal : ¬ geometry.LegalContact rowPose77 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row77_reject_checked)
theorem row77_classified : RowClassified 77 := by
  intro p generated legal
  have he : rowPose77 = p := Option.some.inj (row77_generated.symm.trans generated)
  subst p
  exact (row77_illegal legal).elim

def rowPose78 : Pose 7 := ⟨perm95, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row78_fields : pairFieldsMatchB 188160 facet0 facet68 key0 key78 rowPose78 = true := by decide +kernel
theorem row78_generated : rootPair 78 = some rowPose78 :=
  pairFieldsMatchB_sound (by decide) row78_fields
theorem row78_source : sourceKey 78 ∈ geometry.profile (sourceOwner 78) := by decide +kernel
theorem row78_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 68 key1).FastValid geometry rowPose78 := by decide +kernel
theorem row78_illegal : ¬ geometry.LegalContact rowPose78 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row78_reject_checked)
theorem row78_classified : RowClassified 78 := by
  intro p generated legal
  have he : rowPose78 = p := Option.some.inj (row78_generated.symm.trans generated)
  subst p
  exact (row78_illegal legal).elim

def rowPose79 : Pose 7 := ⟨perm111, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row79_fields : pairFieldsMatchB 188160 facet0 facet69 key0 key79 rowPose79 = true := by decide +kernel
theorem row79_generated : rootPair 79 = some rowPose79 :=
  pairFieldsMatchB_sound (by decide) row79_fields
theorem row79_source : sourceKey 79 ∈ geometry.profile (sourceOwner 79) := by decide +kernel
theorem row79_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 69 key0).FastValid geometry rowPose79 := by decide +kernel
theorem row79_illegal : ¬ geometry.LegalContact rowPose79 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row79_reject_checked)
theorem row79_classified : RowClassified 79 := by
  intro p generated legal
  have he : rowPose79 = p := Option.some.inj (row79_generated.symm.trans generated)
  subst p
  exact (row79_illegal legal).elim

def rowPose80 : Pose 7 := ⟨perm10, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row80_fields : pairFieldsMatchB 188160 facet0 facet70 key0 key80 rowPose80 = true := by decide +kernel
theorem row80_generated : rootPair 80 = some rowPose80 :=
  pairFieldsMatchB_sound (by decide) row80_fields
theorem row80_source : sourceKey 80 ∈ geometry.profile (sourceOwner 80) := by decide +kernel
theorem row80_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 70 key0).FastValid geometry rowPose80 := by decide +kernel
theorem row80_illegal : ¬ geometry.LegalContact rowPose80 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row80_reject_checked)
theorem row80_classified : RowClassified 80 := by
  intro p generated legal
  have he : rowPose80 = p := Option.some.inj (row80_generated.symm.trans generated)
  subst p
  exact (row80_illegal legal).elim

def rowPose81 : Pose 7 := ⟨perm22, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row81_fields : pairFieldsMatchB 188160 facet0 facet71 key0 key81 rowPose81 = true := by decide +kernel
theorem row81_generated : rootPair 81 = some rowPose81 :=
  pairFieldsMatchB_sound (by decide) row81_fields
theorem row81_source : sourceKey 81 ∈ geometry.profile (sourceOwner 81) := by decide +kernel
theorem row81_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 71 key1).FastValid geometry rowPose81 := by decide +kernel
theorem row81_illegal : ¬ geometry.LegalContact rowPose81 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row81_reject_checked)
theorem row81_classified : RowClassified 81 := by
  intro p generated legal
  have he : rowPose81 = p := Option.some.inj (row81_generated.symm.trans generated)
  subst p
  exact (row81_illegal legal).elim

def rowPose82 : Pose 7 := ⟨perm37, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row82_fields : pairFieldsMatchB 188160 facet0 facet72 key0 key82 rowPose82 = true := by decide +kernel
theorem row82_generated : rootPair 82 = some rowPose82 :=
  pairFieldsMatchB_sound (by decide) row82_fields
theorem row82_source : sourceKey 82 ∈ geometry.profile (sourceOwner 82) := by decide +kernel
theorem row82_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 72 key0).FastValid geometry rowPose82 := by decide +kernel
theorem row82_illegal : ¬ geometry.LegalContact rowPose82 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row82_reject_checked)
theorem row82_classified : RowClassified 82 := by
  intro p generated legal
  have he : rowPose82 = p := Option.some.inj (row82_generated.symm.trans generated)
  subst p
  exact (row82_illegal legal).elim

def rowPose83 : Pose 7 := ⟨perm58, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row83_fields : pairFieldsMatchB 188160 facet0 facet73 key0 key83 rowPose83 = true := by decide +kernel
theorem row83_generated : rootPair 83 = some rowPose83 :=
  pairFieldsMatchB_sound (by decide) row83_fields
theorem row83_source : sourceKey 83 ∈ geometry.profile (sourceOwner 83) := by decide +kernel
theorem row83_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 73 key0).FastValid geometry rowPose83 := by decide +kernel
theorem row83_illegal : ¬ geometry.LegalContact rowPose83 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row83_reject_checked)
theorem row83_classified : RowClassified 83 := by
  intro p generated legal
  have he : rowPose83 = p := Option.some.inj (row83_generated.symm.trans generated)
  subst p
  exact (row83_illegal legal).elim

def rowPose84 : Pose 7 := ⟨perm74, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row84_fields : pairFieldsMatchB 188160 facet0 facet74 key0 key84 rowPose84 = true := by decide +kernel
theorem row84_generated : rootPair 84 = some rowPose84 :=
  pairFieldsMatchB_sound (by decide) row84_fields
theorem row84_source : sourceKey 84 ∈ geometry.profile (sourceOwner 84) := by decide +kernel
theorem row84_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 74 key0).FastValid geometry rowPose84 := by decide +kernel
theorem row84_illegal : ¬ geometry.LegalContact rowPose84 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row84_reject_checked)
theorem row84_classified : RowClassified 84 := by
  intro p generated legal
  have he : rowPose84 = p := Option.some.inj (row84_generated.symm.trans generated)
  subst p
  exact (row84_illegal legal).elim

def rowPose85 : Pose 7 := ⟨perm69, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row85_fields : pairFieldsMatchB 188160 facet0 facet74 key0 key85 rowPose85 = true := by decide +kernel
theorem row85_generated : rootPair 85 = some rowPose85 :=
  pairFieldsMatchB_sound (by decide) row85_fields
theorem row85_source : sourceKey 85 ∈ geometry.profile (sourceOwner 85) := by decide +kernel
theorem row85_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 60 key8).FastValid geometry rowPose85 := by decide +kernel
theorem row85_illegal : ¬ geometry.LegalContact rowPose85 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row85_reject_checked)
theorem row85_classified : RowClassified 85 := by
  intro p generated legal
  have he : rowPose85 = p := Option.some.inj (row85_generated.symm.trans generated)
  subst p
  exact (row85_illegal legal).elim

def rowPose86 : Pose 7 := ⟨perm87, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row86_fields : pairFieldsMatchB 188160 facet0 facet75 key0 key86 rowPose86 = true := by decide +kernel
theorem row86_generated : rootPair 86 = some rowPose86 :=
  pairFieldsMatchB_sound (by decide) row86_fields
theorem row86_source : sourceKey 86 ∈ geometry.profile (sourceOwner 86) := by decide +kernel
theorem row86_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 75 key1).FastValid geometry rowPose86 := by decide +kernel
theorem row86_illegal : ¬ geometry.LegalContact rowPose86 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row86_reject_checked)
theorem row86_classified : RowClassified 86 := by
  intro p generated legal
  have he : rowPose86 = p := Option.some.inj (row86_generated.symm.trans generated)
  subst p
  exact (row86_illegal legal).elim

def rowPose87 : Pose 7 := ⟨perm96, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row87_fields : pairFieldsMatchB 188160 facet0 facet76 key0 key87 rowPose87 = true := by decide +kernel
theorem row87_generated : rootPair 87 = some rowPose87 :=
  pairFieldsMatchB_sound (by decide) row87_fields
theorem row87_source : sourceKey 87 ∈ geometry.profile (sourceOwner 87) := by decide +kernel
theorem row87_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 76 key1).FastValid geometry rowPose87 := by decide +kernel
theorem row87_illegal : ¬ geometry.LegalContact rowPose87 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row87_reject_checked)
theorem row87_classified : RowClassified 87 := by
  intro p generated legal
  have he : rowPose87 = p := Option.some.inj (row87_generated.symm.trans generated)
  subst p
  exact (row87_illegal legal).elim

def rowPose88 : Pose 7 := ⟨perm0, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row88_fields : pairFieldsMatchB 188160 facet0 facet77 key0 key88 rowPose88 = true := by decide +kernel
theorem row88_generated : rootPair 88 = some rowPose88 :=
  pairFieldsMatchB_sound (by decide) row88_fields
theorem row88_source : sourceKey 88 ∈ geometry.profile (sourceOwner 88) := by decide +kernel
theorem row88_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 70 key8).FastValid geometry rowPose88 := by decide +kernel
theorem row88_illegal : ¬ geometry.LegalContact rowPose88 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row88_reject_checked)
theorem row88_classified : RowClassified 88 := by
  intro p generated legal
  have he : rowPose88 = p := Option.some.inj (row88_generated.symm.trans generated)
  subst p
  exact (row88_illegal legal).elim

def rowPose89 : Pose 7 := ⟨perm15, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row89_fields : pairFieldsMatchB 188160 facet0 facet77 key0 key89 rowPose89 = true := by decide +kernel
theorem row89_generated : rootPair 89 = some rowPose89 :=
  pairFieldsMatchB_sound (by decide) row89_fields
theorem row89_source : sourceKey 89 ∈ geometry.profile (sourceOwner 89) := by decide +kernel
theorem row89_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 77 key0).FastValid geometry rowPose89 := by decide +kernel
theorem row89_illegal : ¬ geometry.LegalContact rowPose89 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row89_reject_checked)
theorem row89_classified : RowClassified 89 := by
  intro p generated legal
  have he : rowPose89 = p := Option.some.inj (row89_generated.symm.trans generated)
  subst p
  exact (row89_illegal legal).elim

def rowPose90 : Pose 7 := ⟨perm21, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row90_fields : pairFieldsMatchB 188160 facet0 facet78 key0 key90 rowPose90 = true := by decide +kernel
theorem row90_generated : rootPair 90 = some rowPose90 :=
  pairFieldsMatchB_sound (by decide) row90_fields
theorem row90_source : sourceKey 90 ∈ geometry.profile (sourceOwner 90) := by decide +kernel
theorem row90_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 78 key0).FastValid geometry rowPose90 := by decide +kernel
theorem row90_illegal : ¬ geometry.LegalContact rowPose90 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row90_reject_checked)
theorem row90_classified : RowClassified 90 := by
  intro p generated legal
  have he : rowPose90 = p := Option.some.inj (row90_generated.symm.trans generated)
  subst p
  exact (row90_illegal legal).elim

def rowPose91 : Pose 7 := ⟨perm42, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row91_fields : pairFieldsMatchB 188160 facet0 facet79 key0 key91 rowPose91 = true := by decide +kernel
theorem row91_generated : rootPair 91 = some rowPose91 :=
  pairFieldsMatchB_sound (by decide) row91_fields
theorem row91_source : sourceKey 91 ∈ geometry.profile (sourceOwner 91) := by decide +kernel
theorem row91_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 79 key0).FastValid geometry rowPose91 := by decide +kernel
theorem row91_illegal : ¬ geometry.LegalContact rowPose91 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row91_reject_checked)
theorem row91_classified : RowClassified 91 := by
  intro p generated legal
  have he : rowPose91 = p := Option.some.inj (row91_generated.symm.trans generated)
  subst p
  exact (row91_illegal legal).elim

def rowPose92 : Pose 7 := ⟨perm55, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row92_fields : pairFieldsMatchB 188160 facet0 facet80 key0 key92 rowPose92 = true := by decide +kernel
theorem row92_generated : rootPair 92 = some rowPose92 :=
  pairFieldsMatchB_sound (by decide) row92_fields
theorem row92_source : sourceKey 92 ∈ geometry.profile (sourceOwner 92) := by decide +kernel
theorem row92_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 80 key1).FastValid geometry rowPose92 := by decide +kernel
theorem row92_illegal : ¬ geometry.LegalContact rowPose92 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row92_reject_checked)
theorem row92_classified : RowClassified 92 := by
  intro p generated legal
  have he : rowPose92 = p := Option.some.inj (row92_generated.symm.trans generated)
  subst p
  exact (row92_illegal legal).elim

def rowPose93 : Pose 7 := ⟨perm73, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row93_fields : pairFieldsMatchB 188160 facet0 facet81 key0 key93 rowPose93 = true := by decide +kernel
theorem row93_generated : rootPair 93 = some rowPose93 :=
  pairFieldsMatchB_sound (by decide) row93_fields
theorem row93_source : sourceKey 93 ∈ geometry.profile (sourceOwner 93) := by decide +kernel
theorem row93_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 81 key0).FastValid geometry rowPose93 := by decide +kernel
theorem row93_illegal : ¬ geometry.LegalContact rowPose93 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row93_reject_checked)
theorem row93_classified : RowClassified 93 := by
  intro p generated legal
  have he : rowPose93 = p := Option.some.inj (row93_generated.symm.trans generated)
  subst p
  exact (row93_illegal legal).elim

def rowPose94 : Pose 7 := ⟨perm87, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row94_fields : pairFieldsMatchB 188160 facet0 facet82 key0 key94 rowPose94 = true := by decide +kernel
theorem row94_generated : rootPair 94 = some rowPose94 :=
  pairFieldsMatchB_sound (by decide) row94_fields
theorem row94_source : sourceKey 94 ∈ geometry.profile (sourceOwner 94) := by decide +kernel
theorem row94_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 82 key1).FastValid geometry rowPose94 := by decide +kernel
theorem row94_illegal : ¬ geometry.LegalContact rowPose94 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row94_reject_checked)
theorem row94_classified : RowClassified 94 := by
  intro p generated legal
  have he : rowPose94 = p := Option.some.inj (row94_generated.symm.trans generated)
  subst p
  exact (row94_illegal legal).elim

def rowPose95 : Pose 7 := ⟨perm96, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row95_fields : pairFieldsMatchB 188160 facet0 facet83 key0 key95 rowPose95 = true := by decide +kernel
theorem row95_generated : rootPair 95 = some rowPose95 :=
  pairFieldsMatchB_sound (by decide) row95_fields
theorem row95_source : sourceKey 95 ∈ geometry.profile (sourceOwner 95) := by decide +kernel
theorem row95_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 83 key1).FastValid geometry rowPose95 := by decide +kernel
theorem row95_illegal : ¬ geometry.LegalContact rowPose95 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row95_reject_checked)
theorem row95_classified : RowClassified 95 := by
  intro p generated legal
  have he : rowPose95 = p := Option.some.inj (row95_generated.symm.trans generated)
  subst p
  exact (row95_illegal legal).elim

theorem chunk02_classified (i : Fin 32) : RowClassified ⟨64 + i.val, by omega⟩ := by
  fin_cases i
  · exact row64_classified
  · exact row65_classified
  · exact row66_classified
  · exact row67_classified
  · exact row68_classified
  · exact row69_classified
  · exact row70_classified
  · exact row71_classified
  · exact row72_classified
  · exact row73_classified
  · exact row74_classified
  · exact row75_classified
  · exact row76_classified
  · exact row77_classified
  · exact row78_classified
  · exact row79_classified
  · exact row80_classified
  · exact row81_classified
  · exact row82_classified
  · exact row83_classified
  · exact row84_classified
  · exact row85_classified
  · exact row86_classified
  · exact row87_classified
  · exact row88_classified
  · exact row89_classified
  · exact row90_classified
  · exact row91_classified
  · exact row92_classified
  · exact row93_classified
  · exact row94_classified
  · exact row95_classified

theorem chunk02_source (i : Fin 32) : sourceKey ⟨64 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨64 + i.val, by omega⟩) := by
  fin_cases i
  · exact row64_source
  · exact row65_source
  · exact row66_source
  · exact row67_source
  · exact row68_source
  · exact row69_source
  · exact row70_source
  · exact row71_source
  · exact row72_source
  · exact row73_source
  · exact row74_source
  · exact row75_source
  · exact row76_source
  · exact row77_source
  · exact row78_source
  · exact row79_source
  · exact row80_source
  · exact row81_source
  · exact row82_source
  · exact row83_source
  · exact row84_source
  · exact row85_source
  · exact row86_source
  · exact row87_source
  · exact row88_source
  · exact row89_source
  · exact row90_source
  · exact row91_source
  · exact row92_source
  · exact row93_source
  · exact row94_source
  · exact row95_source

#print axioms chunk02_classified
end SparseMonotiles.Contact.RootZeroPilot7
