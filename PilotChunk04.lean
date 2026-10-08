module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose128 : Pose 7 := ⟨perm15, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row128_fields : pairFieldsMatchB 188160 facet0 facet112 key0 key128 rowPose128 = true := by decide +kernel
theorem row128_generated : rootPair 128 = some rowPose128 :=
  pairFieldsMatchB_sound (by decide) row128_fields
theorem row128_source : sourceKey 128 ∈ geometry.profile (sourceOwner 128) := by decide +kernel
theorem row128_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 112 key1).FastValid geometry rowPose128 := by decide +kernel
theorem row128_illegal : ¬ geometry.LegalContact rowPose128 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row128_reject_checked)
theorem row128_classified : RowClassified 128 := by
  intro p generated legal
  have he : rowPose128 = p := Option.some.inj (row128_generated.symm.trans generated)
  subst p
  exact (row128_illegal legal).elim

def rowPose129 : Pose 7 := ⟨perm24, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row129_fields : pairFieldsMatchB 188160 facet0 facet113 key0 key129 rowPose129 = true := by decide +kernel
theorem row129_generated : rootPair 129 = some rowPose129 :=
  pairFieldsMatchB_sound (by decide) row129_fields
theorem row129_source : sourceKey 129 ∈ geometry.profile (sourceOwner 129) := by decide +kernel
theorem row129_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 113 key1).FastValid geometry rowPose129 := by decide +kernel
theorem row129_illegal : ¬ geometry.LegalContact rowPose129 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row129_reject_checked)
theorem row129_classified : RowClassified 129 := by
  intro p generated legal
  have he : rowPose129 = p := Option.some.inj (row129_generated.symm.trans generated)
  subst p
  exact (row129_illegal legal).elim

def rowPose130 : Pose 7 := ⟨perm37, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row130_fields : pairFieldsMatchB 188160 facet0 facet114 key0 key130 rowPose130 = true := by decide +kernel
theorem row130_generated : rootPair 130 = some rowPose130 :=
  pairFieldsMatchB_sound (by decide) row130_fields
theorem row130_source : sourceKey 130 ∈ geometry.profile (sourceOwner 130) := by decide +kernel
theorem row130_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 114 key0).FastValid geometry rowPose130 := by decide +kernel
theorem row130_illegal : ¬ geometry.LegalContact rowPose130 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row130_reject_checked)
theorem row130_classified : RowClassified 130 := by
  intro p generated legal
  have he : rowPose130 = p := Option.some.inj (row130_generated.symm.trans generated)
  subst p
  exact (row130_illegal legal).elim

def rowPose131 : Pose 7 := ⟨perm42, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row131_fields : pairFieldsMatchB 188160 facet0 facet114 key0 key131 rowPose131 = true := by decide +kernel
theorem row131_generated : rootPair 131 = some rowPose131 :=
  pairFieldsMatchB_sound (by decide) row131_fields
theorem row131_source : sourceKey 131 ∈ geometry.profile (sourceOwner 131) := by decide +kernel
theorem row131_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 338 key8).FastValid geometry rowPose131 := by decide +kernel
theorem row131_illegal : ¬ geometry.LegalContact rowPose131 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row131_reject_checked)
theorem row131_classified : RowClassified 131 := by
  intro p generated legal
  have he : rowPose131 = p := Option.some.inj (row131_generated.symm.trans generated)
  subst p
  exact (row131_illegal legal).elim

def rowPose132 : Pose 7 := ⟨perm53, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row132_fields : pairFieldsMatchB 188160 facet0 facet115 key0 key132 rowPose132 = true := by decide +kernel
theorem row132_generated : rootPair 132 = some rowPose132 :=
  pairFieldsMatchB_sound (by decide) row132_fields
theorem row132_source : sourceKey 132 ∈ geometry.profile (sourceOwner 132) := by decide +kernel
theorem row132_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 115 key0).FastValid geometry rowPose132 := by decide +kernel
theorem row132_illegal : ¬ geometry.LegalContact rowPose132 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row132_reject_checked)
theorem row132_classified : RowClassified 132 := by
  intro p generated legal
  have he : rowPose132 = p := Option.some.inj (row132_generated.symm.trans generated)
  subst p
  exact (row132_illegal legal).elim

def rowPose133 : Pose 7 := ⟨perm74, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row133_fields : pairFieldsMatchB 188160 facet0 facet116 key0 key133 rowPose133 = true := by decide +kernel
theorem row133_generated : rootPair 133 = some rowPose133 :=
  pairFieldsMatchB_sound (by decide) row133_fields
theorem row133_source : sourceKey 133 ∈ geometry.profile (sourceOwner 133) := by decide +kernel
theorem row133_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 116 key0).FastValid geometry rowPose133 := by decide +kernel
theorem row133_illegal : ¬ geometry.LegalContact rowPose133 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row133_reject_checked)
theorem row133_classified : RowClassified 133 := by
  intro p generated legal
  have he : rowPose133 = p := Option.some.inj (row133_generated.symm.trans generated)
  subst p
  exact (row133_illegal legal).elim

def rowPose134 : Pose 7 := ⟨perm89, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row134_fields : pairFieldsMatchB 188160 facet0 facet117 key0 key134 rowPose134 = true := by decide +kernel
theorem row134_generated : rootPair 134 = some rowPose134 :=
  pairFieldsMatchB_sound (by decide) row134_fields
theorem row134_source : sourceKey 134 ∈ geometry.profile (sourceOwner 134) := by decide +kernel
theorem row134_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 117 key1).FastValid geometry rowPose134 := by decide +kernel
theorem row134_illegal : ¬ geometry.LegalContact rowPose134 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row134_reject_checked)
theorem row134_classified : RowClassified 134 := by
  intro p generated legal
  have he : rowPose134 = p := Option.some.inj (row134_generated.symm.trans generated)
  subst p
  exact (row134_illegal legal).elim

def rowPose135 : Pose 7 := ⟨perm101, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row135_fields : pairFieldsMatchB 188160 facet0 facet118 key0 key135 rowPose135 = true := by decide +kernel
theorem row135_generated : rootPair 135 = some rowPose135 :=
  pairFieldsMatchB_sound (by decide) row135_fields
theorem row135_source : sourceKey 135 ∈ geometry.profile (sourceOwner 135) := by decide +kernel
theorem row135_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 118 key0).FastValid geometry rowPose135 := by decide +kernel
theorem row135_illegal : ¬ geometry.LegalContact rowPose135 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row135_reject_checked)
theorem row135_classified : RowClassified 135 := by
  intro p generated legal
  have he : rowPose135 = p := Option.some.inj (row135_generated.symm.trans generated)
  subst p
  exact (row135_illegal legal).elim

def rowPose136 : Pose 7 := ⟨perm10, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row136_fields : pairFieldsMatchB 188160 facet0 facet119 key0 key136 rowPose136 = true := by decide +kernel
theorem row136_generated : rootPair 136 = some rowPose136 :=
  pairFieldsMatchB_sound (by decide) row136_fields
theorem row136_source : sourceKey 136 ∈ geometry.profile (sourceOwner 136) := by decide +kernel
theorem row136_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 119 key0).FastValid geometry rowPose136 := by decide +kernel
theorem row136_illegal : ¬ geometry.LegalContact rowPose136 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row136_reject_checked)
theorem row136_classified : RowClassified 136 := by
  intro p generated legal
  have he : rowPose136 = p := Option.some.inj (row136_generated.symm.trans generated)
  subst p
  exact (row136_illegal legal).elim

def rowPose137 : Pose 7 := ⟨perm22, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row137_fields : pairFieldsMatchB 188160 facet0 facet120 key0 key137 rowPose137 = true := by decide +kernel
theorem row137_generated : rootPair 137 = some rowPose137 :=
  pairFieldsMatchB_sound (by decide) row137_fields
theorem row137_source : sourceKey 137 ∈ geometry.profile (sourceOwner 137) := by decide +kernel
theorem row137_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 120 key1).FastValid geometry rowPose137 := by decide +kernel
theorem row137_illegal : ¬ geometry.LegalContact rowPose137 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row137_reject_checked)
theorem row137_classified : RowClassified 137 := by
  intro p generated legal
  have he : rowPose137 = p := Option.some.inj (row137_generated.symm.trans generated)
  subst p
  exact (row137_illegal legal).elim

def rowPose138 : Pose 7 := ⟨perm37, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row138_fields : pairFieldsMatchB 188160 facet0 facet121 key0 key138 rowPose138 = true := by decide +kernel
theorem row138_generated : rootPair 138 = some rowPose138 :=
  pairFieldsMatchB_sound (by decide) row138_fields
theorem row138_source : sourceKey 138 ∈ geometry.profile (sourceOwner 138) := by decide +kernel
theorem row138_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 121 key0).FastValid geometry rowPose138 := by decide +kernel
theorem row138_illegal : ¬ geometry.LegalContact rowPose138 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row138_reject_checked)
theorem row138_classified : RowClassified 138 := by
  intro p generated legal
  have he : rowPose138 = p := Option.some.inj (row138_generated.symm.trans generated)
  subst p
  exact (row138_illegal legal).elim

def rowPose139 : Pose 7 := ⟨perm58, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row139_fields : pairFieldsMatchB 188160 facet0 facet122 key0 key139 rowPose139 = true := by decide +kernel
theorem row139_generated : rootPair 139 = some rowPose139 :=
  pairFieldsMatchB_sound (by decide) row139_fields
theorem row139_source : sourceKey 139 ∈ geometry.profile (sourceOwner 139) := by decide +kernel
theorem row139_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 122 key0).FastValid geometry rowPose139 := by decide +kernel
theorem row139_illegal : ¬ geometry.LegalContact rowPose139 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row139_reject_checked)
theorem row139_classified : RowClassified 139 := by
  intro p generated legal
  have he : rowPose139 = p := Option.some.inj (row139_generated.symm.trans generated)
  subst p
  exact (row139_illegal legal).elim

def rowPose140 : Pose 7 := ⟨perm74, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row140_fields : pairFieldsMatchB 188160 facet0 facet123 key0 key140 rowPose140 = true := by decide +kernel
theorem row140_generated : rootPair 140 = some rowPose140 :=
  pairFieldsMatchB_sound (by decide) row140_fields
theorem row140_source : sourceKey 140 ∈ geometry.profile (sourceOwner 140) := by decide +kernel
theorem row140_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 123 key0).FastValid geometry rowPose140 := by decide +kernel
theorem row140_illegal : ¬ geometry.LegalContact rowPose140 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row140_reject_checked)
theorem row140_classified : RowClassified 140 := by
  intro p generated legal
  have he : rowPose140 = p := Option.some.inj (row140_generated.symm.trans generated)
  subst p
  exact (row140_illegal legal).elim

def rowPose141 : Pose 7 := ⟨perm69, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row141_fields : pairFieldsMatchB 188160 facet0 facet123 key0 key141 rowPose141 = true := by decide +kernel
theorem row141_generated : rootPair 141 = some rowPose141 :=
  pairFieldsMatchB_sound (by decide) row141_fields
theorem row141_source : sourceKey 141 ∈ geometry.profile (sourceOwner 141) := by decide +kernel
theorem row141_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 137 key8).FastValid geometry rowPose141 := by decide +kernel
theorem row141_illegal : ¬ geometry.LegalContact rowPose141 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row141_reject_checked)
theorem row141_classified : RowClassified 141 := by
  intro p generated legal
  have he : rowPose141 = p := Option.some.inj (row141_generated.symm.trans generated)
  subst p
  exact (row141_illegal legal).elim

def rowPose142 : Pose 7 := ⟨perm87, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row142_fields : pairFieldsMatchB 188160 facet0 facet124 key0 key142 rowPose142 = true := by decide +kernel
theorem row142_generated : rootPair 142 = some rowPose142 :=
  pairFieldsMatchB_sound (by decide) row142_fields
theorem row142_source : sourceKey 142 ∈ geometry.profile (sourceOwner 142) := by decide +kernel
theorem row142_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 124 key1).FastValid geometry rowPose142 := by decide +kernel
theorem row142_illegal : ¬ geometry.LegalContact rowPose142 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row142_reject_checked)
theorem row142_classified : RowClassified 142 := by
  intro p generated legal
  have he : rowPose142 = p := Option.some.inj (row142_generated.symm.trans generated)
  subst p
  exact (row142_illegal legal).elim

def rowPose143 : Pose 7 := ⟨perm96, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row143_fields : pairFieldsMatchB 188160 facet0 facet125 key0 key143 rowPose143 = true := by decide +kernel
theorem row143_generated : rootPair 143 = some rowPose143 :=
  pairFieldsMatchB_sound (by decide) row143_fields
theorem row143_source : sourceKey 143 ∈ geometry.profile (sourceOwner 143) := by decide +kernel
theorem row143_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 125 key1).FastValid geometry rowPose143 := by decide +kernel
theorem row143_illegal : ¬ geometry.LegalContact rowPose143 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row143_reject_checked)
theorem row143_classified : RowClassified 143 := by
  intro p generated legal
  have he : rowPose143 = p := Option.some.inj (row143_generated.symm.trans generated)
  subst p
  exact (row143_illegal legal).elim

def rowPose144 : Pose 7 := ⟨perm0, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row144_fields : pairFieldsMatchB 188160 facet0 facet126 key0 key144 rowPose144 = true := by decide +kernel
theorem row144_generated : rootPair 144 = some rowPose144 :=
  pairFieldsMatchB_sound (by decide) row144_fields
theorem row144_source : sourceKey 144 ∈ geometry.profile (sourceOwner 144) := by decide +kernel
theorem row144_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 126 key0).FastValid geometry rowPose144 := by decide +kernel
theorem row144_illegal : ¬ geometry.LegalContact rowPose144 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row144_reject_checked)
theorem row144_classified : RowClassified 144 := by
  intro p generated legal
  have he : rowPose144 = p := Option.some.inj (row144_generated.symm.trans generated)
  subst p
  exact (row144_illegal legal).elim

def rowPose145 : Pose 7 := ⟨perm15, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row145_fields : pairFieldsMatchB 188160 facet0 facet126 key0 key145 rowPose145 = true := by decide +kernel
theorem row145_generated : rootPair 145 = some rowPose145 :=
  pairFieldsMatchB_sound (by decide) row145_fields
theorem row145_source : sourceKey 145 ∈ geometry.profile (sourceOwner 145) := by decide +kernel
theorem row145_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 350 key8).FastValid geometry rowPose145 := by decide +kernel
theorem row145_illegal : ¬ geometry.LegalContact rowPose145 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row145_reject_checked)
theorem row145_classified : RowClassified 145 := by
  intro p generated legal
  have he : rowPose145 = p := Option.some.inj (row145_generated.symm.trans generated)
  subst p
  exact (row145_illegal legal).elim

def rowPose146 : Pose 7 := ⟨perm21, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row146_fields : pairFieldsMatchB 188160 facet0 facet127 key0 key146 rowPose146 = true := by decide +kernel
theorem row146_generated : rootPair 146 = some rowPose146 :=
  pairFieldsMatchB_sound (by decide) row146_fields
theorem row146_source : sourceKey 146 ∈ geometry.profile (sourceOwner 146) := by decide +kernel
theorem row146_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 127 key1).FastValid geometry rowPose146 := by decide +kernel
theorem row146_illegal : ¬ geometry.LegalContact rowPose146 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row146_reject_checked)
theorem row146_classified : RowClassified 146 := by
  intro p generated legal
  have he : rowPose146 = p := Option.some.inj (row146_generated.symm.trans generated)
  subst p
  exact (row146_illegal legal).elim

def rowPose147 : Pose 7 := ⟨perm42, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row147_fields : pairFieldsMatchB 188160 facet0 facet128 key0 key147 rowPose147 = true := by decide +kernel
theorem row147_generated : rootPair 147 = some rowPose147 :=
  pairFieldsMatchB_sound (by decide) row147_fields
theorem row147_source : sourceKey 147 ∈ geometry.profile (sourceOwner 147) := by decide +kernel
theorem row147_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 128 key1).FastValid geometry rowPose147 := by decide +kernel
theorem row147_illegal : ¬ geometry.LegalContact rowPose147 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row147_reject_checked)
theorem row147_classified : RowClassified 147 := by
  intro p generated legal
  have he : rowPose147 = p := Option.some.inj (row147_generated.symm.trans generated)
  subst p
  exact (row147_illegal legal).elim

def rowPose148 : Pose 7 := ⟨perm55, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row148_fields : pairFieldsMatchB 188160 facet0 facet129 key0 key148 rowPose148 = true := by decide +kernel
theorem row148_generated : rootPair 148 = some rowPose148 :=
  pairFieldsMatchB_sound (by decide) row148_fields
theorem row148_source : sourceKey 148 ∈ geometry.profile (sourceOwner 148) := by decide +kernel
theorem row148_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 129 key0).FastValid geometry rowPose148 := by decide +kernel
theorem row148_illegal : ¬ geometry.LegalContact rowPose148 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row148_reject_checked)
theorem row148_classified : RowClassified 148 := by
  intro p generated legal
  have he : rowPose148 = p := Option.some.inj (row148_generated.symm.trans generated)
  subst p
  exact (row148_illegal legal).elim

def rowPose149 : Pose 7 := ⟨perm73, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row149_fields : pairFieldsMatchB 188160 facet0 facet130 key0 key149 rowPose149 = true := by decide +kernel
theorem row149_generated : rootPair 149 = some rowPose149 :=
  pairFieldsMatchB_sound (by decide) row149_fields
theorem row149_source : sourceKey 149 ∈ geometry.profile (sourceOwner 149) := by decide +kernel
theorem row149_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 130 key1).FastValid geometry rowPose149 := by decide +kernel
theorem row149_illegal : ¬ geometry.LegalContact rowPose149 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row149_reject_checked)
theorem row149_classified : RowClassified 149 := by
  intro p generated legal
  have he : rowPose149 = p := Option.some.inj (row149_generated.symm.trans generated)
  subst p
  exact (row149_illegal legal).elim

def rowPose150 : Pose 7 := ⟨perm87, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row150_fields : pairFieldsMatchB 188160 facet0 facet131 key0 key150 rowPose150 = true := by decide +kernel
theorem row150_generated : rootPair 150 = some rowPose150 :=
  pairFieldsMatchB_sound (by decide) row150_fields
theorem row150_source : sourceKey 150 ∈ geometry.profile (sourceOwner 150) := by decide +kernel
theorem row150_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 131 key0).FastValid geometry rowPose150 := by decide +kernel
theorem row150_illegal : ¬ geometry.LegalContact rowPose150 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row150_reject_checked)
theorem row150_classified : RowClassified 150 := by
  intro p generated legal
  have he : rowPose150 = p := Option.some.inj (row150_generated.symm.trans generated)
  subst p
  exact (row150_illegal legal).elim

def rowPose151 : Pose 7 := ⟨perm96, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row151_fields : pairFieldsMatchB 188160 facet0 facet132 key0 key151 rowPose151 = true := by decide +kernel
theorem row151_generated : rootPair 151 = some rowPose151 :=
  pairFieldsMatchB_sound (by decide) row151_fields
theorem row151_source : sourceKey 151 ∈ geometry.profile (sourceOwner 151) := by decide +kernel
theorem row151_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 132 key0).FastValid geometry rowPose151 := by decide +kernel
theorem row151_illegal : ¬ geometry.LegalContact rowPose151 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row151_reject_checked)
theorem row151_classified : RowClassified 151 := by
  intro p generated legal
  have he : rowPose151 = p := Option.some.inj (row151_generated.symm.trans generated)
  subst p
  exact (row151_illegal legal).elim

def rowPose152 : Pose 7 := ⟨perm15, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row152_fields : pairFieldsMatchB 188160 facet0 facet133 key0 key152 rowPose152 = true := by decide +kernel
theorem row152_generated : rootPair 152 = some rowPose152 :=
  pairFieldsMatchB_sound (by decide) row152_fields
theorem row152_source : sourceKey 152 ∈ geometry.profile (sourceOwner 152) := by decide +kernel
theorem row152_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 133 key1).FastValid geometry rowPose152 := by decide +kernel
theorem row152_illegal : ¬ geometry.LegalContact rowPose152 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row152_reject_checked)
theorem row152_classified : RowClassified 152 := by
  intro p generated legal
  have he : rowPose152 = p := Option.some.inj (row152_generated.symm.trans generated)
  subst p
  exact (row152_illegal legal).elim

def rowPose153 : Pose 7 := ⟨perm24, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row153_fields : pairFieldsMatchB 188160 facet0 facet134 key0 key153 rowPose153 = true := by decide +kernel
theorem row153_generated : rootPair 153 = some rowPose153 :=
  pairFieldsMatchB_sound (by decide) row153_fields
theorem row153_source : sourceKey 153 ∈ geometry.profile (sourceOwner 153) := by decide +kernel
theorem row153_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 134 key1).FastValid geometry rowPose153 := by decide +kernel
theorem row153_illegal : ¬ geometry.LegalContact rowPose153 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row153_reject_checked)
theorem row153_classified : RowClassified 153 := by
  intro p generated legal
  have he : rowPose153 = p := Option.some.inj (row153_generated.symm.trans generated)
  subst p
  exact (row153_illegal legal).elim

def rowPose154 : Pose 7 := ⟨perm37, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row154_fields : pairFieldsMatchB 188160 facet0 facet135 key0 key154 rowPose154 = true := by decide +kernel
theorem row154_generated : rootPair 154 = some rowPose154 :=
  pairFieldsMatchB_sound (by decide) row154_fields
theorem row154_source : sourceKey 154 ∈ geometry.profile (sourceOwner 154) := by decide +kernel
theorem row154_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 135 key0).FastValid geometry rowPose154 := by decide +kernel
theorem row154_illegal : ¬ geometry.LegalContact rowPose154 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row154_reject_checked)
theorem row154_classified : RowClassified 154 := by
  intro p generated legal
  have he : rowPose154 = p := Option.some.inj (row154_generated.symm.trans generated)
  subst p
  exact (row154_illegal legal).elim

def rowPose155 : Pose 7 := ⟨perm42, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row155_fields : pairFieldsMatchB 188160 facet0 facet135 key0 key155 rowPose155 = true := by decide +kernel
theorem row155_generated : rootPair 155 = some rowPose155 :=
  pairFieldsMatchB_sound (by decide) row155_fields
theorem row155_source : sourceKey 155 ∈ geometry.profile (sourceOwner 155) := by decide +kernel
theorem row155_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 359 key8).FastValid geometry rowPose155 := by decide +kernel
theorem row155_illegal : ¬ geometry.LegalContact rowPose155 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row155_reject_checked)
theorem row155_classified : RowClassified 155 := by
  intro p generated legal
  have he : rowPose155 = p := Option.some.inj (row155_generated.symm.trans generated)
  subst p
  exact (row155_illegal legal).elim

def rowPose156 : Pose 7 := ⟨perm53, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row156_fields : pairFieldsMatchB 188160 facet0 facet136 key0 key156 rowPose156 = true := by decide +kernel
theorem row156_generated : rootPair 156 = some rowPose156 :=
  pairFieldsMatchB_sound (by decide) row156_fields
theorem row156_source : sourceKey 156 ∈ geometry.profile (sourceOwner 156) := by decide +kernel
theorem row156_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 136 key0).FastValid geometry rowPose156 := by decide +kernel
theorem row156_illegal : ¬ geometry.LegalContact rowPose156 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row156_reject_checked)
theorem row156_classified : RowClassified 156 := by
  intro p generated legal
  have he : rowPose156 = p := Option.some.inj (row156_generated.symm.trans generated)
  subst p
  exact (row156_illegal legal).elim

def rowPose157 : Pose 7 := ⟨perm74, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row157_fields : pairFieldsMatchB 188160 facet0 facet137 key0 key157 rowPose157 = true := by decide +kernel
theorem row157_generated : rootPair 157 = some rowPose157 :=
  pairFieldsMatchB_sound (by decide) row157_fields
theorem row157_source : sourceKey 157 ∈ geometry.profile (sourceOwner 157) := by decide +kernel
theorem row157_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 137 key0).FastValid geometry rowPose157 := by decide +kernel
theorem row157_illegal : ¬ geometry.LegalContact rowPose157 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row157_reject_checked)
theorem row157_classified : RowClassified 157 := by
  intro p generated legal
  have he : rowPose157 = p := Option.some.inj (row157_generated.symm.trans generated)
  subst p
  exact (row157_illegal legal).elim

def rowPose158 : Pose 7 := ⟨perm89, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row158_fields : pairFieldsMatchB 188160 facet0 facet138 key0 key158 rowPose158 = true := by decide +kernel
theorem row158_generated : rootPair 158 = some rowPose158 :=
  pairFieldsMatchB_sound (by decide) row158_fields
theorem row158_source : sourceKey 158 ∈ geometry.profile (sourceOwner 158) := by decide +kernel
theorem row158_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 138 key1).FastValid geometry rowPose158 := by decide +kernel
theorem row158_illegal : ¬ geometry.LegalContact rowPose158 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row158_reject_checked)
theorem row158_classified : RowClassified 158 := by
  intro p generated legal
  have he : rowPose158 = p := Option.some.inj (row158_generated.symm.trans generated)
  subst p
  exact (row158_illegal legal).elim

def rowPose159 : Pose 7 := ⟨perm101, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row159_fields : pairFieldsMatchB 188160 facet0 facet139 key0 key159 rowPose159 = true := by decide +kernel
theorem row159_generated : rootPair 159 = some rowPose159 :=
  pairFieldsMatchB_sound (by decide) row159_fields
theorem row159_source : sourceKey 159 ∈ geometry.profile (sourceOwner 159) := by decide +kernel
theorem row159_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 139 key0).FastValid geometry rowPose159 := by decide +kernel
theorem row159_illegal : ¬ geometry.LegalContact rowPose159 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row159_reject_checked)
theorem row159_classified : RowClassified 159 := by
  intro p generated legal
  have he : rowPose159 = p := Option.some.inj (row159_generated.symm.trans generated)
  subst p
  exact (row159_illegal legal).elim

theorem chunk04_classified (i : Fin 32) : RowClassified ⟨128 + i.val, by omega⟩ := by
  fin_cases i
  · exact row128_classified
  · exact row129_classified
  · exact row130_classified
  · exact row131_classified
  · exact row132_classified
  · exact row133_classified
  · exact row134_classified
  · exact row135_classified
  · exact row136_classified
  · exact row137_classified
  · exact row138_classified
  · exact row139_classified
  · exact row140_classified
  · exact row141_classified
  · exact row142_classified
  · exact row143_classified
  · exact row144_classified
  · exact row145_classified
  · exact row146_classified
  · exact row147_classified
  · exact row148_classified
  · exact row149_classified
  · exact row150_classified
  · exact row151_classified
  · exact row152_classified
  · exact row153_classified
  · exact row154_classified
  · exact row155_classified
  · exact row156_classified
  · exact row157_classified
  · exact row158_classified
  · exact row159_classified

theorem chunk04_source (i : Fin 32) : sourceKey ⟨128 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨128 + i.val, by omega⟩) := by
  fin_cases i
  · exact row128_source
  · exact row129_source
  · exact row130_source
  · exact row131_source
  · exact row132_source
  · exact row133_source
  · exact row134_source
  · exact row135_source
  · exact row136_source
  · exact row137_source
  · exact row138_source
  · exact row139_source
  · exact row140_source
  · exact row141_source
  · exact row142_source
  · exact row143_source
  · exact row144_source
  · exact row145_source
  · exact row146_source
  · exact row147_source
  · exact row148_source
  · exact row149_source
  · exact row150_source
  · exact row151_source
  · exact row152_source
  · exact row153_source
  · exact row154_source
  · exact row155_source
  · exact row156_source
  · exact row157_source
  · exact row158_source
  · exact row159_source

#print axioms chunk04_classified
end SparseMonotiles.Contact.RootZeroPilot7
