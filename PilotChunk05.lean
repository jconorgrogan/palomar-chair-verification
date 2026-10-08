module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose160 : Pose 7 := ⟨perm5, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row160_fields : pairFieldsMatchB 188160 facet0 facet140 key0 key160 rowPose160 = true := by decide +kernel
theorem row160_generated : rootPair 160 = some rowPose160 :=
  pairFieldsMatchB_sound (by decide) row160_fields
theorem row160_source : sourceKey 160 ∈ geometry.profile (sourceOwner 160) := by decide +kernel
theorem row160_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 140 key1).FastValid geometry rowPose160 := by decide +kernel
theorem row160_illegal : ¬ geometry.LegalContact rowPose160 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row160_reject_checked)
theorem row160_classified : RowClassified 160 := by
  intro p generated legal
  have he : rowPose160 = p := Option.some.inj (row160_generated.symm.trans generated)
  subst p
  exact (row160_illegal legal).elim

def rowPose161 : Pose 7 := ⟨perm21, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row161_fields : pairFieldsMatchB 188160 facet0 facet141 key0 key161 rowPose161 = true := by decide +kernel
theorem row161_generated : rootPair 161 = some rowPose161 :=
  pairFieldsMatchB_sound (by decide) row161_fields
theorem row161_source : sourceKey 161 ∈ geometry.profile (sourceOwner 161) := by decide +kernel
theorem row161_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 141 key0).FastValid geometry rowPose161 := by decide +kernel
theorem row161_illegal : ¬ geometry.LegalContact rowPose161 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row161_reject_checked)
theorem row161_classified : RowClassified 161 := by
  intro p generated legal
  have he : rowPose161 = p := Option.some.inj (row161_generated.symm.trans generated)
  subst p
  exact (row161_illegal legal).elim

def rowPose162 : Pose 7 := ⟨perm42, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row162_fields : pairFieldsMatchB 188160 facet0 facet142 key0 key162 rowPose162 = true := by decide +kernel
theorem row162_generated : rootPair 162 = some rowPose162 :=
  pairFieldsMatchB_sound (by decide) row162_fields
theorem row162_source : sourceKey 162 ∈ geometry.profile (sourceOwner 162) := by decide +kernel
theorem row162_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 142 key0).FastValid geometry rowPose162 := by decide +kernel
theorem row162_illegal : ¬ geometry.LegalContact rowPose162 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row162_reject_checked)
theorem row162_classified : RowClassified 162 := by
  intro p generated legal
  have he : rowPose162 = p := Option.some.inj (row162_generated.symm.trans generated)
  subst p
  exact (row162_illegal legal).elim

def rowPose163 : Pose 7 := ⟨perm53, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row163_fields : pairFieldsMatchB 188160 facet0 facet143 key0 key163 rowPose163 = true := by decide +kernel
theorem row163_generated : rootPair 163 = some rowPose163 :=
  pairFieldsMatchB_sound (by decide) row163_fields
theorem row163_source : sourceKey 163 ∈ geometry.profile (sourceOwner 163) := by decide +kernel
theorem row163_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 115 key8).FastValid geometry rowPose163 := by decide +kernel
theorem row163_illegal : ¬ geometry.LegalContact rowPose163 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row163_reject_checked)
theorem row163_classified : RowClassified 163 := by
  intro p generated legal
  have he : rowPose163 = p := Option.some.inj (row163_generated.symm.trans generated)
  subst p
  exact (row163_illegal legal).elim

def rowPose164 : Pose 7 := ⟨perm58, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row164_fields : pairFieldsMatchB 188160 facet0 facet143 key0 key164 rowPose164 = true := by decide +kernel
theorem row164_generated : rootPair 164 = some rowPose164 :=
  pairFieldsMatchB_sound (by decide) row164_fields
theorem row164_source : sourceKey 164 ∈ geometry.profile (sourceOwner 164) := by decide +kernel
theorem row164_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 143 key0).FastValid geometry rowPose164 := by decide +kernel
theorem row164_illegal : ¬ geometry.LegalContact rowPose164 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row164_reject_checked)
theorem row164_classified : RowClassified 164 := by
  intro p generated legal
  have he : rowPose164 = p := Option.some.inj (row164_generated.symm.trans generated)
  subst p
  exact (row164_illegal legal).elim

def rowPose165 : Pose 7 := ⟨perm69, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row165_fields : pairFieldsMatchB 188160 facet0 facet144 key0 key165 rowPose165 = true := by decide +kernel
theorem row165_generated : rootPair 165 = some rowPose165 :=
  pairFieldsMatchB_sound (by decide) row165_fields
theorem row165_source : sourceKey 165 ∈ geometry.profile (sourceOwner 165) := by decide +kernel
theorem row165_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 144 key1).FastValid geometry rowPose165 := by decide +kernel
theorem row165_illegal : ¬ geometry.LegalContact rowPose165 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row165_reject_checked)
theorem row165_classified : RowClassified 165 := by
  intro p generated legal
  have he : rowPose165 = p := Option.some.inj (row165_generated.symm.trans generated)
  subst p
  exact (row165_illegal legal).elim

def rowPose166 : Pose 7 := ⟨perm90, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row166_fields : pairFieldsMatchB 188160 facet0 facet145 key0 key166 rowPose166 = true := by decide +kernel
theorem row166_generated : rootPair 166 = some rowPose166 :=
  pairFieldsMatchB_sound (by decide) row166_fields
theorem row166_source : sourceKey 166 ∈ geometry.profile (sourceOwner 166) := by decide +kernel
theorem row166_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 145 key1).FastValid geometry rowPose166 := by decide +kernel
theorem row166_illegal : ¬ geometry.LegalContact rowPose166 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row166_reject_checked)
theorem row166_classified : RowClassified 166 := by
  intro p generated legal
  have he : rowPose166 = p := Option.some.inj (row166_generated.symm.trans generated)
  subst p
  exact (row166_illegal legal).elim

def rowPose167 : Pose 7 := ⟨perm106, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row167_fields : pairFieldsMatchB 188160 facet0 facet146 key0 key167 rowPose167 = true := by decide +kernel
theorem row167_generated : rootPair 167 = some rowPose167 :=
  pairFieldsMatchB_sound (by decide) row167_fields
theorem row167_source : sourceKey 167 ∈ geometry.profile (sourceOwner 167) := by decide +kernel
theorem row167_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 146 key0).FastValid geometry rowPose167 := by decide +kernel
theorem row167_illegal : ¬ geometry.LegalContact rowPose167 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row167_reject_checked)
theorem row167_classified : RowClassified 167 := by
  intro p generated legal
  have he : rowPose167 = p := Option.some.inj (row167_generated.symm.trans generated)
  subst p
  exact (row167_illegal legal).elim

def rowPose168 : Pose 7 := ⟨perm10, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row168_fields : pairFieldsMatchB 188160 facet0 facet147 key0 key168 rowPose168 = true := by decide +kernel
theorem row168_generated : rootPair 168 = some rowPose168 :=
  pairFieldsMatchB_sound (by decide) row168_fields
theorem row168_source : sourceKey 168 ∈ geometry.profile (sourceOwner 168) := by decide +kernel
theorem row168_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 147 key1).FastValid geometry rowPose168 := by decide +kernel
theorem row168_illegal : ¬ geometry.LegalContact rowPose168 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row168_reject_checked)
theorem row168_classified : RowClassified 168 := by
  intro p generated legal
  have he : rowPose168 = p := Option.some.inj (row168_generated.symm.trans generated)
  subst p
  exact (row168_illegal legal).elim

def rowPose169 : Pose 7 := ⟨perm22, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row169_fields : pairFieldsMatchB 188160 facet0 facet148 key0 key169 rowPose169 = true := by decide +kernel
theorem row169_generated : rootPair 169 = some rowPose169 :=
  pairFieldsMatchB_sound (by decide) row169_fields
theorem row169_source : sourceKey 169 ∈ geometry.profile (sourceOwner 169) := by decide +kernel
theorem row169_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 148 key0).FastValid geometry rowPose169 := by decide +kernel
theorem row169_illegal : ¬ geometry.LegalContact rowPose169 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row169_reject_checked)
theorem row169_classified : RowClassified 169 := by
  intro p generated legal
  have he : rowPose169 = p := Option.some.inj (row169_generated.symm.trans generated)
  subst p
  exact (row169_illegal legal).elim

def rowPose170 : Pose 7 := ⟨perm37, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row170_fields : pairFieldsMatchB 188160 facet0 facet149 key0 key170 rowPose170 = true := by decide +kernel
theorem row170_generated : rootPair 170 = some rowPose170 :=
  pairFieldsMatchB_sound (by decide) row170_fields
theorem row170_source : sourceKey 170 ∈ geometry.profile (sourceOwner 170) := by decide +kernel
theorem row170_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 149 key1).FastValid geometry rowPose170 := by decide +kernel
theorem row170_illegal : ¬ geometry.LegalContact rowPose170 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row170_reject_checked)
theorem row170_classified : RowClassified 170 := by
  intro p generated legal
  have he : rowPose170 = p := Option.some.inj (row170_generated.symm.trans generated)
  subst p
  exact (row170_illegal legal).elim

def rowPose171 : Pose 7 := ⟨perm58, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row171_fields : pairFieldsMatchB 188160 facet0 facet150 key0 key171 rowPose171 = true := by decide +kernel
theorem row171_generated : rootPair 171 = some rowPose171 :=
  pairFieldsMatchB_sound (by decide) row171_fields
theorem row171_source : sourceKey 171 ∈ geometry.profile (sourceOwner 171) := by decide +kernel
theorem row171_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 150 key1).FastValid geometry rowPose171 := by decide +kernel
theorem row171_illegal : ¬ geometry.LegalContact rowPose171 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row171_reject_checked)
theorem row171_classified : RowClassified 171 := by
  intro p generated legal
  have he : rowPose171 = p := Option.some.inj (row171_generated.symm.trans generated)
  subst p
  exact (row171_illegal legal).elim

def rowPose172 : Pose 7 := ⟨perm74, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row172_fields : pairFieldsMatchB 188160 facet0 facet151 key0 key172 rowPose172 = true := by decide +kernel
theorem row172_generated : rootPair 172 = some rowPose172 :=
  pairFieldsMatchB_sound (by decide) row172_fields
theorem row172_source : sourceKey 172 ∈ geometry.profile (sourceOwner 172) := by decide +kernel
theorem row172_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 207 key8).FastValid geometry rowPose172 := by decide +kernel
theorem row172_illegal : ¬ geometry.LegalContact rowPose172 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row172_reject_checked)
theorem row172_classified : RowClassified 172 := by
  intro p generated legal
  have he : rowPose172 = p := Option.some.inj (row172_generated.symm.trans generated)
  subst p
  exact (row172_illegal legal).elim

def rowPose173 : Pose 7 := ⟨perm69, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row173_fields : pairFieldsMatchB 188160 facet0 facet151 key0 key173 rowPose173 = true := by decide +kernel
theorem row173_generated : rootPair 173 = some rowPose173 :=
  pairFieldsMatchB_sound (by decide) row173_fields
theorem row173_source : sourceKey 173 ∈ geometry.profile (sourceOwner 173) := by decide +kernel
theorem row173_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 151 key0).FastValid geometry rowPose173 := by decide +kernel
theorem row173_illegal : ¬ geometry.LegalContact rowPose173 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row173_reject_checked)
theorem row173_classified : RowClassified 173 := by
  intro p generated legal
  have he : rowPose173 = p := Option.some.inj (row173_generated.symm.trans generated)
  subst p
  exact (row173_illegal legal).elim

def rowPose174 : Pose 7 := ⟨perm87, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row174_fields : pairFieldsMatchB 188160 facet0 facet152 key0 key174 rowPose174 = true := by decide +kernel
theorem row174_generated : rootPair 174 = some rowPose174 :=
  pairFieldsMatchB_sound (by decide) row174_fields
theorem row174_source : sourceKey 174 ∈ geometry.profile (sourceOwner 174) := by decide +kernel
theorem row174_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 152 key0).FastValid geometry rowPose174 := by decide +kernel
theorem row174_illegal : ¬ geometry.LegalContact rowPose174 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row174_reject_checked)
theorem row174_classified : RowClassified 174 := by
  intro p generated legal
  have he : rowPose174 = p := Option.some.inj (row174_generated.symm.trans generated)
  subst p
  exact (row174_illegal legal).elim

def rowPose175 : Pose 7 := ⟨perm96, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row175_fields : pairFieldsMatchB 188160 facet0 facet153 key0 key175 rowPose175 = true := by decide +kernel
theorem row175_generated : rootPair 175 = some rowPose175 :=
  pairFieldsMatchB_sound (by decide) row175_fields
theorem row175_source : sourceKey 175 ∈ geometry.profile (sourceOwner 175) := by decide +kernel
theorem row175_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 153 key0).FastValid geometry rowPose175 := by decide +kernel
theorem row175_illegal : ¬ geometry.LegalContact rowPose175 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row175_reject_checked)
theorem row175_classified : RowClassified 175 := by
  intro p generated legal
  have he : rowPose175 = p := Option.some.inj (row175_generated.symm.trans generated)
  subst p
  exact (row175_illegal legal).elim

def rowPose176 : Pose 7 := ⟨perm15, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row176_fields : pairFieldsMatchB 188160 facet0 facet154 key0 key176 rowPose176 = true := by decide +kernel
theorem row176_generated : rootPair 176 = some rowPose176 :=
  pairFieldsMatchB_sound (by decide) row176_fields
theorem row176_source : sourceKey 176 ∈ geometry.profile (sourceOwner 176) := by decide +kernel
theorem row176_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 154 key0).FastValid geometry rowPose176 := by decide +kernel
theorem row176_illegal : ¬ geometry.LegalContact rowPose176 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row176_reject_checked)
theorem row176_classified : RowClassified 176 := by
  intro p generated legal
  have he : rowPose176 = p := Option.some.inj (row176_generated.symm.trans generated)
  subst p
  exact (row176_illegal legal).elim

def rowPose177 : Pose 7 := ⟨perm24, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row177_fields : pairFieldsMatchB 188160 facet0 facet155 key0 key177 rowPose177 = true := by decide +kernel
theorem row177_generated : rootPair 177 = some rowPose177 :=
  pairFieldsMatchB_sound (by decide) row177_fields
theorem row177_source : sourceKey 177 ∈ geometry.profile (sourceOwner 177) := by decide +kernel
theorem row177_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 155 key0).FastValid geometry rowPose177 := by decide +kernel
theorem row177_illegal : ¬ geometry.LegalContact rowPose177 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row177_reject_checked)
theorem row177_classified : RowClassified 177 := by
  intro p generated legal
  have he : rowPose177 = p := Option.some.inj (row177_generated.symm.trans generated)
  subst p
  exact (row177_illegal legal).elim

def rowPose178 : Pose 7 := ⟨perm38, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row178_fields : pairFieldsMatchB 188160 facet0 facet156 key0 key178 rowPose178 = true := by decide +kernel
theorem row178_generated : rootPair 178 = some rowPose178 :=
  pairFieldsMatchB_sound (by decide) row178_fields
theorem row178_source : sourceKey 178 ∈ geometry.profile (sourceOwner 178) := by decide +kernel
theorem row178_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 156 key1).FastValid geometry rowPose178 := by decide +kernel
theorem row178_illegal : ¬ geometry.LegalContact rowPose178 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row178_reject_checked)
theorem row178_classified : RowClassified 178 := by
  intro p generated legal
  have he : rowPose178 = p := Option.some.inj (row178_generated.symm.trans generated)
  subst p
  exact (row178_illegal legal).elim

def rowPose179 : Pose 7 := ⟨perm56, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row179_fields : pairFieldsMatchB 188160 facet0 facet157 key0 key179 rowPose179 = true := by decide +kernel
theorem row179_generated : rootPair 179 = some rowPose179 :=
  pairFieldsMatchB_sound (by decide) row179_fields
theorem row179_source : sourceKey 179 ∈ geometry.profile (sourceOwner 179) := by decide +kernel
theorem row179_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 157 key0).FastValid geometry rowPose179 := by decide +kernel
theorem row179_illegal : ¬ geometry.LegalContact rowPose179 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row179_reject_checked)
theorem row179_classified : RowClassified 179 := by
  intro p generated legal
  have he : rowPose179 = p := Option.some.inj (row179_generated.symm.trans generated)
  subst p
  exact (row179_illegal legal).elim

def rowPose180 : Pose 7 := ⟨perm69, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row180_fields : pairFieldsMatchB 188160 facet0 facet158 key0 key180 rowPose180 = true := by decide +kernel
theorem row180_generated : rootPair 180 = some rowPose180 :=
  pairFieldsMatchB_sound (by decide) row180_fields
theorem row180_source : sourceKey 180 ∈ geometry.profile (sourceOwner 180) := by decide +kernel
theorem row180_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 158 key1).FastValid geometry rowPose180 := by decide +kernel
theorem row180_illegal : ¬ geometry.LegalContact rowPose180 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row180_reject_checked)
theorem row180_classified : RowClassified 180 := by
  intro p generated legal
  have he : rowPose180 = p := Option.some.inj (row180_generated.symm.trans generated)
  subst p
  exact (row180_illegal legal).elim

def rowPose181 : Pose 7 := ⟨perm90, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row181_fields : pairFieldsMatchB 188160 facet0 facet159 key0 key181 rowPose181 = true := by decide +kernel
theorem row181_generated : rootPair 181 = some rowPose181 :=
  pairFieldsMatchB_sound (by decide) row181_fields
theorem row181_source : sourceKey 181 ∈ geometry.profile (sourceOwner 181) := by decide +kernel
theorem row181_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 159 key1).FastValid geometry rowPose181 := by decide +kernel
theorem row181_illegal : ¬ geometry.LegalContact rowPose181 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row181_reject_checked)
theorem row181_classified : RowClassified 181 := by
  intro p generated legal
  have he : rowPose181 = p := Option.some.inj (row181_generated.symm.trans generated)
  subst p
  exact (row181_illegal legal).elim

def rowPose182 : Pose 7 := ⟨perm96, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row182_fields : pairFieldsMatchB 188160 facet0 facet160 key0 key182 rowPose182 = true := by decide +kernel
theorem row182_generated : rootPair 182 = some rowPose182 :=
  pairFieldsMatchB_sound (by decide) row182_fields
theorem row182_source : sourceKey 182 ∈ geometry.profile (sourceOwner 182) := by decide +kernel
theorem row182_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 146 key8).FastValid geometry rowPose182 := by decide +kernel
theorem row182_illegal : ¬ geometry.LegalContact rowPose182 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row182_reject_checked)
theorem row182_classified : RowClassified 182 := by
  intro p generated legal
  have he : rowPose182 = p := Option.some.inj (row182_generated.symm.trans generated)
  subst p
  exact (row182_illegal legal).elim

def rowPose183 : Pose 7 := ⟨perm111, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row183_fields : pairFieldsMatchB 188160 facet0 facet160 key0 key183 rowPose183 = true := by decide +kernel
theorem row183_generated : rootPair 183 = some rowPose183 :=
  pairFieldsMatchB_sound (by decide) row183_fields
theorem row183_source : sourceKey 183 ∈ geometry.profile (sourceOwner 183) := by decide +kernel
theorem row183_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 160 key0).FastValid geometry rowPose183 := by decide +kernel
theorem row183_illegal : ¬ geometry.LegalContact rowPose183 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row183_reject_checked)
theorem row183_classified : RowClassified 183 := by
  intro p generated legal
  have he : rowPose183 = p := Option.some.inj (row183_generated.symm.trans generated)
  subst p
  exact (row183_illegal legal).elim

def rowPose184 : Pose 7 := ⟨perm15, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row184_fields : pairFieldsMatchB 188160 facet0 facet161 key0 key184 rowPose184 = true := by decide +kernel
theorem row184_generated : rootPair 184 = some rowPose184 :=
  pairFieldsMatchB_sound (by decide) row184_fields
theorem row184_source : sourceKey 184 ∈ geometry.profile (sourceOwner 184) := by decide +kernel
theorem row184_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 161 key1).FastValid geometry rowPose184 := by decide +kernel
theorem row184_illegal : ¬ geometry.LegalContact rowPose184 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row184_reject_checked)
theorem row184_classified : RowClassified 184 := by
  intro p generated legal
  have he : rowPose184 = p := Option.some.inj (row184_generated.symm.trans generated)
  subst p
  exact (row184_illegal legal).elim

def rowPose185 : Pose 7 := ⟨perm24, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row185_fields : pairFieldsMatchB 188160 facet0 facet162 key0 key185 rowPose185 = true := by decide +kernel
theorem row185_generated : rootPair 185 = some rowPose185 :=
  pairFieldsMatchB_sound (by decide) row185_fields
theorem row185_source : sourceKey 185 ∈ geometry.profile (sourceOwner 185) := by decide +kernel
theorem row185_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 162 key1).FastValid geometry rowPose185 := by decide +kernel
theorem row185_illegal : ¬ geometry.LegalContact rowPose185 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row185_reject_checked)
theorem row185_classified : RowClassified 185 := by
  intro p generated legal
  have he : rowPose185 = p := Option.some.inj (row185_generated.symm.trans generated)
  subst p
  exact (row185_illegal legal).elim

def rowPose186 : Pose 7 := ⟨perm38, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row186_fields : pairFieldsMatchB 188160 facet0 facet163 key0 key186 rowPose186 = true := by decide +kernel
theorem row186_generated : rootPair 186 = some rowPose186 :=
  pairFieldsMatchB_sound (by decide) row186_fields
theorem row186_source : sourceKey 186 ∈ geometry.profile (sourceOwner 186) := by decide +kernel
theorem row186_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 163 key0).FastValid geometry rowPose186 := by decide +kernel
theorem row186_illegal : ¬ geometry.LegalContact rowPose186 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row186_reject_checked)
theorem row186_classified : RowClassified 186 := by
  intro p generated legal
  have he : rowPose186 = p := Option.some.inj (row186_generated.symm.trans generated)
  subst p
  exact (row186_illegal legal).elim

def rowPose187 : Pose 7 := ⟨perm56, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row187_fields : pairFieldsMatchB 188160 facet0 facet164 key0 key187 rowPose187 = true := by decide +kernel
theorem row187_generated : rootPair 187 = some rowPose187 :=
  pairFieldsMatchB_sound (by decide) row187_fields
theorem row187_source : sourceKey 187 ∈ geometry.profile (sourceOwner 187) := by decide +kernel
theorem row187_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 164 key1).FastValid geometry rowPose187 := by decide +kernel
theorem row187_illegal : ¬ geometry.LegalContact rowPose187 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row187_reject_checked)
theorem row187_classified : RowClassified 187 := by
  intro p generated legal
  have he : rowPose187 = p := Option.some.inj (row187_generated.symm.trans generated)
  subst p
  exact (row187_illegal legal).elim

def rowPose188 : Pose 7 := ⟨perm69, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row188_fields : pairFieldsMatchB 188160 facet0 facet165 key0 key188 rowPose188 = true := by decide +kernel
theorem row188_generated : rootPair 188 = some rowPose188 :=
  pairFieldsMatchB_sound (by decide) row188_fields
theorem row188_source : sourceKey 188 ∈ geometry.profile (sourceOwner 188) := by decide +kernel
theorem row188_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 165 key0).FastValid geometry rowPose188 := by decide +kernel
theorem row188_illegal : ¬ geometry.LegalContact rowPose188 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row188_reject_checked)
theorem row188_classified : RowClassified 188 := by
  intro p generated legal
  have he : rowPose188 = p := Option.some.inj (row188_generated.symm.trans generated)
  subst p
  exact (row188_illegal legal).elim

def rowPose189 : Pose 7 := ⟨perm90, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row189_fields : pairFieldsMatchB 188160 facet0 facet166 key0 key189 rowPose189 = true := by decide +kernel
theorem row189_generated : rootPair 189 = some rowPose189 :=
  pairFieldsMatchB_sound (by decide) row189_fields
theorem row189_source : sourceKey 189 ∈ geometry.profile (sourceOwner 189) := by decide +kernel
theorem row189_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 166 key0).FastValid geometry rowPose189 := by decide +kernel
theorem row189_illegal : ¬ geometry.LegalContact rowPose189 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row189_reject_checked)
theorem row189_classified : RowClassified 189 := by
  intro p generated legal
  have he : rowPose189 = p := Option.some.inj (row189_generated.symm.trans generated)
  subst p
  exact (row189_illegal legal).elim

def rowPose190 : Pose 7 := ⟨perm96, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row190_fields : pairFieldsMatchB 188160 facet0 facet167 key0 key190 rowPose190 = true := by decide +kernel
theorem row190_generated : rootPair 190 = some rowPose190 :=
  pairFieldsMatchB_sound (by decide) row190_fields
theorem row190_source : sourceKey 190 ∈ geometry.profile (sourceOwner 190) := by decide +kernel
theorem row190_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 167 key0).FastValid geometry rowPose190 := by decide +kernel
theorem row190_illegal : ¬ geometry.LegalContact rowPose190 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row190_reject_checked)
theorem row190_classified : RowClassified 190 := by
  intro p generated legal
  have he : rowPose190 = p := Option.some.inj (row190_generated.symm.trans generated)
  subst p
  exact (row190_illegal legal).elim

def rowPose191 : Pose 7 := ⟨perm111, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row191_fields : pairFieldsMatchB 188160 facet0 facet167 key0 key191 rowPose191 = true := by decide +kernel
theorem row191_generated : rootPair 191 = some rowPose191 :=
  pairFieldsMatchB_sound (by decide) row191_fields
theorem row191_source : sourceKey 191 ∈ geometry.profile (sourceOwner 191) := by decide +kernel
theorem row191_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 616 key8).FastValid geometry rowPose191 := by decide +kernel
theorem row191_illegal : ¬ geometry.LegalContact rowPose191 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row191_reject_checked)
theorem row191_classified : RowClassified 191 := by
  intro p generated legal
  have he : rowPose191 = p := Option.some.inj (row191_generated.symm.trans generated)
  subst p
  exact (row191_illegal legal).elim

theorem chunk05_classified (i : Fin 32) : RowClassified ⟨160 + i.val, by omega⟩ := by
  fin_cases i
  · exact row160_classified
  · exact row161_classified
  · exact row162_classified
  · exact row163_classified
  · exact row164_classified
  · exact row165_classified
  · exact row166_classified
  · exact row167_classified
  · exact row168_classified
  · exact row169_classified
  · exact row170_classified
  · exact row171_classified
  · exact row172_classified
  · exact row173_classified
  · exact row174_classified
  · exact row175_classified
  · exact row176_classified
  · exact row177_classified
  · exact row178_classified
  · exact row179_classified
  · exact row180_classified
  · exact row181_classified
  · exact row182_classified
  · exact row183_classified
  · exact row184_classified
  · exact row185_classified
  · exact row186_classified
  · exact row187_classified
  · exact row188_classified
  · exact row189_classified
  · exact row190_classified
  · exact row191_classified

theorem chunk05_source (i : Fin 32) : sourceKey ⟨160 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨160 + i.val, by omega⟩) := by
  fin_cases i
  · exact row160_source
  · exact row161_source
  · exact row162_source
  · exact row163_source
  · exact row164_source
  · exact row165_source
  · exact row166_source
  · exact row167_source
  · exact row168_source
  · exact row169_source
  · exact row170_source
  · exact row171_source
  · exact row172_source
  · exact row173_source
  · exact row174_source
  · exact row175_source
  · exact row176_source
  · exact row177_source
  · exact row178_source
  · exact row179_source
  · exact row180_source
  · exact row181_source
  · exact row182_source
  · exact row183_source
  · exact row184_source
  · exact row185_source
  · exact row186_source
  · exact row187_source
  · exact row188_source
  · exact row189_source
  · exact row190_source
  · exact row191_source

#print axioms chunk05_classified
end SparseMonotiles.Contact.RootZeroPilot7
