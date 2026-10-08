module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose224 : Pose 7 := ⟨perm5, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row224_fields : pairFieldsMatchB 188160 facet0 facet196 key0 key224 rowPose224 = true := by decide +kernel
theorem row224_generated : rootPair 224 = some rowPose224 :=
  pairFieldsMatchB_sound (by decide) row224_fields
theorem row224_source : sourceKey 224 ∈ geometry.profile (sourceOwner 224) := by decide +kernel
theorem row224_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 196 key0).FastValid geometry rowPose224 := by decide +kernel
theorem row224_illegal : ¬ geometry.LegalContact rowPose224 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row224_reject_checked)
theorem row224_classified : RowClassified 224 := by
  intro p generated legal
  have he : rowPose224 = p := Option.some.inj (row224_generated.symm.trans generated)
  subst p
  exact (row224_illegal legal).elim

def rowPose225 : Pose 7 := ⟨perm21, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row225_fields : pairFieldsMatchB 188160 facet0 facet197 key0 key225 rowPose225 = true := by decide +kernel
theorem row225_generated : rootPair 225 = some rowPose225 :=
  pairFieldsMatchB_sound (by decide) row225_fields
theorem row225_source : sourceKey 225 ∈ geometry.profile (sourceOwner 225) := by decide +kernel
theorem row225_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 197 key1).FastValid geometry rowPose225 := by decide +kernel
theorem row225_illegal : ¬ geometry.LegalContact rowPose225 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row225_reject_checked)
theorem row225_classified : RowClassified 225 := by
  intro p generated legal
  have he : rowPose225 = p := Option.some.inj (row225_generated.symm.trans generated)
  subst p
  exact (row225_illegal legal).elim

def rowPose226 : Pose 7 := ⟨perm42, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row226_fields : pairFieldsMatchB 188160 facet0 facet198 key0 key226 rowPose226 = true := by decide +kernel
theorem row226_generated : rootPair 226 = some rowPose226 :=
  pairFieldsMatchB_sound (by decide) row226_fields
theorem row226_source : sourceKey 226 ∈ geometry.profile (sourceOwner 226) := by decide +kernel
theorem row226_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 198 key1).FastValid geometry rowPose226 := by decide +kernel
theorem row226_illegal : ¬ geometry.LegalContact rowPose226 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row226_reject_checked)
theorem row226_classified : RowClassified 226 := by
  intro p generated legal
  have he : rowPose226 = p := Option.some.inj (row226_generated.symm.trans generated)
  subst p
  exact (row226_illegal legal).elim

def rowPose227 : Pose 7 := ⟨perm53, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row227_fields : pairFieldsMatchB 188160 facet0 facet199 key0 key227 rowPose227 = true := by decide +kernel
theorem row227_generated : rootPair 227 = some rowPose227 :=
  pairFieldsMatchB_sound (by decide) row227_fields
theorem row227_source : sourceKey 227 ∈ geometry.profile (sourceOwner 227) := by decide +kernel
theorem row227_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 199 key0).FastValid geometry rowPose227 := by decide +kernel
theorem row227_illegal : ¬ geometry.LegalContact rowPose227 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row227_reject_checked)
theorem row227_classified : RowClassified 227 := by
  intro p generated legal
  have he : rowPose227 = p := Option.some.inj (row227_generated.symm.trans generated)
  subst p
  exact (row227_illegal legal).elim

def rowPose228 : Pose 7 := ⟨perm58, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row228_fields : pairFieldsMatchB 188160 facet0 facet199 key0 key228 rowPose228 = true := by decide +kernel
theorem row228_generated : rootPair 228 = some rowPose228 :=
  pairFieldsMatchB_sound (by decide) row228_fields
theorem row228_source : sourceKey 228 ∈ geometry.profile (sourceOwner 228) := by decide +kernel
theorem row228_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 87 key8).FastValid geometry rowPose228 := by decide +kernel
theorem row228_illegal : ¬ geometry.LegalContact rowPose228 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row228_reject_checked)
theorem row228_classified : RowClassified 228 := by
  intro p generated legal
  have he : rowPose228 = p := Option.some.inj (row228_generated.symm.trans generated)
  subst p
  exact (row228_illegal legal).elim

def rowPose229 : Pose 7 := ⟨perm69, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row229_fields : pairFieldsMatchB 188160 facet0 facet200 key0 key229 rowPose229 = true := by decide +kernel
theorem row229_generated : rootPair 229 = some rowPose229 :=
  pairFieldsMatchB_sound (by decide) row229_fields
theorem row229_source : sourceKey 229 ∈ geometry.profile (sourceOwner 229) := by decide +kernel
theorem row229_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 200 key0).FastValid geometry rowPose229 := by decide +kernel
theorem row229_illegal : ¬ geometry.LegalContact rowPose229 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row229_reject_checked)
theorem row229_classified : RowClassified 229 := by
  intro p generated legal
  have he : rowPose229 = p := Option.some.inj (row229_generated.symm.trans generated)
  subst p
  exact (row229_illegal legal).elim

def rowPose230 : Pose 7 := ⟨perm90, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row230_fields : pairFieldsMatchB 188160 facet0 facet201 key0 key230 rowPose230 = true := by decide +kernel
theorem row230_generated : rootPair 230 = some rowPose230 :=
  pairFieldsMatchB_sound (by decide) row230_fields
theorem row230_source : sourceKey 230 ∈ geometry.profile (sourceOwner 230) := by decide +kernel
theorem row230_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 201 key0).FastValid geometry rowPose230 := by decide +kernel
theorem row230_illegal : ¬ geometry.LegalContact rowPose230 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row230_reject_checked)
theorem row230_classified : RowClassified 230 := by
  intro p generated legal
  have he : rowPose230 = p := Option.some.inj (row230_generated.symm.trans generated)
  subst p
  exact (row230_illegal legal).elim

def rowPose231 : Pose 7 := ⟨perm106, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row231_fields : pairFieldsMatchB 188160 facet0 facet202 key0 key231 rowPose231 = true := by decide +kernel
theorem row231_generated : rootPair 231 = some rowPose231 :=
  pairFieldsMatchB_sound (by decide) row231_fields
theorem row231_source : sourceKey 231 ∈ geometry.profile (sourceOwner 231) := by decide +kernel
theorem row231_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 202 key1).FastValid geometry rowPose231 := by decide +kernel
theorem row231_illegal : ¬ geometry.LegalContact rowPose231 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row231_reject_checked)
theorem row231_classified : RowClassified 231 := by
  intro p generated legal
  have he : rowPose231 = p := Option.some.inj (row231_generated.symm.trans generated)
  subst p
  exact (row231_illegal legal).elim

def rowPose232 : Pose 7 := ⟨perm15, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row232_fields : pairFieldsMatchB 188160 facet0 facet203 key0 key232 rowPose232 = true := by decide +kernel
theorem row232_generated : rootPair 232 = some rowPose232 :=
  pairFieldsMatchB_sound (by decide) row232_fields
theorem row232_source : sourceKey 232 ∈ geometry.profile (sourceOwner 232) := by decide +kernel
theorem row232_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 203 key0).FastValid geometry rowPose232 := by decide +kernel
theorem row232_illegal : ¬ geometry.LegalContact rowPose232 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row232_reject_checked)
theorem row232_classified : RowClassified 232 := by
  intro p generated legal
  have he : rowPose232 = p := Option.some.inj (row232_generated.symm.trans generated)
  subst p
  exact (row232_illegal legal).elim

def rowPose233 : Pose 7 := ⟨perm24, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row233_fields : pairFieldsMatchB 188160 facet0 facet204 key0 key233 rowPose233 = true := by decide +kernel
theorem row233_generated : rootPair 233 = some rowPose233 :=
  pairFieldsMatchB_sound (by decide) row233_fields
theorem row233_source : sourceKey 233 ∈ geometry.profile (sourceOwner 233) := by decide +kernel
theorem row233_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 204 key0).FastValid geometry rowPose233 := by decide +kernel
theorem row233_illegal : ¬ geometry.LegalContact rowPose233 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row233_reject_checked)
theorem row233_classified : RowClassified 233 := by
  intro p generated legal
  have he : rowPose233 = p := Option.some.inj (row233_generated.symm.trans generated)
  subst p
  exact (row233_illegal legal).elim

def rowPose234 : Pose 7 := ⟨perm37, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row234_fields : pairFieldsMatchB 188160 facet0 facet205 key0 key234 rowPose234 = true := by decide +kernel
theorem row234_generated : rootPair 234 = some rowPose234 :=
  pairFieldsMatchB_sound (by decide) row234_fields
theorem row234_source : sourceKey 234 ∈ geometry.profile (sourceOwner 234) := by decide +kernel
theorem row234_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 149 key8).FastValid geometry rowPose234 := by decide +kernel
theorem row234_illegal : ¬ geometry.LegalContact rowPose234 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row234_reject_checked)
theorem row234_classified : RowClassified 234 := by
  intro p generated legal
  have he : rowPose234 = p := Option.some.inj (row234_generated.symm.trans generated)
  subst p
  exact (row234_illegal legal).elim

def rowPose235 : Pose 7 := ⟨perm42, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row235_fields : pairFieldsMatchB 188160 facet0 facet205 key0 key235 rowPose235 = true := by decide +kernel
theorem row235_generated : rootPair 235 = some rowPose235 :=
  pairFieldsMatchB_sound (by decide) row235_fields
theorem row235_source : sourceKey 235 ∈ geometry.profile (sourceOwner 235) := by decide +kernel
theorem row235_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 205 key0).FastValid geometry rowPose235 := by decide +kernel
theorem row235_illegal : ¬ geometry.LegalContact rowPose235 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row235_reject_checked)
theorem row235_classified : RowClassified 235 := by
  intro p generated legal
  have he : rowPose235 = p := Option.some.inj (row235_generated.symm.trans generated)
  subst p
  exact (row235_illegal legal).elim

def rowPose236 : Pose 7 := ⟨perm53, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row236_fields : pairFieldsMatchB 188160 facet0 facet206 key0 key236 rowPose236 = true := by decide +kernel
theorem row236_generated : rootPair 236 = some rowPose236 :=
  pairFieldsMatchB_sound (by decide) row236_fields
theorem row236_source : sourceKey 236 ∈ geometry.profile (sourceOwner 236) := by decide +kernel
theorem row236_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 206 key1).FastValid geometry rowPose236 := by decide +kernel
theorem row236_illegal : ¬ geometry.LegalContact rowPose236 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row236_reject_checked)
theorem row236_classified : RowClassified 236 := by
  intro p generated legal
  have he : rowPose236 = p := Option.some.inj (row236_generated.symm.trans generated)
  subst p
  exact (row236_illegal legal).elim

def rowPose237 : Pose 7 := ⟨perm74, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row237_fields : pairFieldsMatchB 188160 facet0 facet207 key0 key237 rowPose237 = true := by decide +kernel
theorem row237_generated : rootPair 237 = some rowPose237 :=
  pairFieldsMatchB_sound (by decide) row237_fields
theorem row237_source : sourceKey 237 ∈ geometry.profile (sourceOwner 237) := by decide +kernel
theorem row237_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 207 key1).FastValid geometry rowPose237 := by decide +kernel
theorem row237_illegal : ¬ geometry.LegalContact rowPose237 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row237_reject_checked)
theorem row237_classified : RowClassified 237 := by
  intro p generated legal
  have he : rowPose237 = p := Option.some.inj (row237_generated.symm.trans generated)
  subst p
  exact (row237_illegal legal).elim

def rowPose238 : Pose 7 := ⟨perm89, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row238_fields : pairFieldsMatchB 188160 facet0 facet208 key0 key238 rowPose238 = true := by decide +kernel
theorem row238_generated : rootPair 238 = some rowPose238 :=
  pairFieldsMatchB_sound (by decide) row238_fields
theorem row238_source : sourceKey 238 ∈ geometry.profile (sourceOwner 238) := by decide +kernel
theorem row238_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 208 key0).FastValid geometry rowPose238 := by decide +kernel
theorem row238_illegal : ¬ geometry.LegalContact rowPose238 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row238_reject_checked)
theorem row238_classified : RowClassified 238 := by
  intro p generated legal
  have he : rowPose238 = p := Option.some.inj (row238_generated.symm.trans generated)
  subst p
  exact (row238_illegal legal).elim

def rowPose239 : Pose 7 := ⟨perm101, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row239_fields : pairFieldsMatchB 188160 facet0 facet209 key0 key239 rowPose239 = true := by decide +kernel
theorem row239_generated : rootPair 239 = some rowPose239 :=
  pairFieldsMatchB_sound (by decide) row239_fields
theorem row239_source : sourceKey 239 ∈ geometry.profile (sourceOwner 239) := by decide +kernel
theorem row239_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 209 key1).FastValid geometry rowPose239 := by decide +kernel
theorem row239_illegal : ¬ geometry.LegalContact rowPose239 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row239_reject_checked)
theorem row239_classified : RowClassified 239 := by
  intro p generated legal
  have he : rowPose239 = p := Option.some.inj (row239_generated.symm.trans generated)
  subst p
  exact (row239_illegal legal).elim

def rowPose240 : Pose 7 := ⟨perm0, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row240_fields : pairFieldsMatchB 188160 facet0 facet210 key0 key240 rowPose240 = true := by decide +kernel
theorem row240_generated : rootPair 240 = some rowPose240 :=
  pairFieldsMatchB_sound (by decide) row240_fields
theorem row240_source : sourceKey 240 ∈ geometry.profile (sourceOwner 240) := by decide +kernel
theorem row240_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 210 key0).FastValid geometry rowPose240 := by decide +kernel
theorem row240_illegal : ¬ geometry.LegalContact rowPose240 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row240_reject_checked)
theorem row240_classified : RowClassified 240 := by
  intro p generated legal
  have he : rowPose240 = p := Option.some.inj (row240_generated.symm.trans generated)
  subst p
  exact (row240_illegal legal).elim

def rowPose241 : Pose 7 := ⟨perm15, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row241_fields : pairFieldsMatchB 188160 facet0 facet210 key0 key241 rowPose241 = true := by decide +kernel
theorem row241_generated : rootPair 241 = some rowPose241 :=
  pairFieldsMatchB_sound (by decide) row241_fields
theorem row241_source : sourceKey 241 ∈ geometry.profile (sourceOwner 241) := by decide +kernel
theorem row241_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 434 key8).FastValid geometry rowPose241 := by decide +kernel
theorem row241_illegal : ¬ geometry.LegalContact rowPose241 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row241_reject_checked)
theorem row241_classified : RowClassified 241 := by
  intro p generated legal
  have he : rowPose241 = p := Option.some.inj (row241_generated.symm.trans generated)
  subst p
  exact (row241_illegal legal).elim

def rowPose242 : Pose 7 := ⟨perm21, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row242_fields : pairFieldsMatchB 188160 facet0 facet211 key0 key242 rowPose242 = true := by decide +kernel
theorem row242_generated : rootPair 242 = some rowPose242 :=
  pairFieldsMatchB_sound (by decide) row242_fields
theorem row242_source : sourceKey 242 ∈ geometry.profile (sourceOwner 242) := by decide +kernel
theorem row242_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 211 key1).FastValid geometry rowPose242 := by decide +kernel
theorem row242_illegal : ¬ geometry.LegalContact rowPose242 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row242_reject_checked)
theorem row242_classified : RowClassified 242 := by
  intro p generated legal
  have he : rowPose242 = p := Option.some.inj (row242_generated.symm.trans generated)
  subst p
  exact (row242_illegal legal).elim

def rowPose243 : Pose 7 := ⟨perm42, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row243_fields : pairFieldsMatchB 188160 facet0 facet212 key0 key243 rowPose243 = true := by decide +kernel
theorem row243_generated : rootPair 243 = some rowPose243 :=
  pairFieldsMatchB_sound (by decide) row243_fields
theorem row243_source : sourceKey 243 ∈ geometry.profile (sourceOwner 243) := by decide +kernel
theorem row243_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 212 key1).FastValid geometry rowPose243 := by decide +kernel
theorem row243_illegal : ¬ geometry.LegalContact rowPose243 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row243_reject_checked)
theorem row243_classified : RowClassified 243 := by
  intro p generated legal
  have he : rowPose243 = p := Option.some.inj (row243_generated.symm.trans generated)
  subst p
  exact (row243_illegal legal).elim

def rowPose244 : Pose 7 := ⟨perm55, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row244_fields : pairFieldsMatchB 188160 facet0 facet213 key0 key244 rowPose244 = true := by decide +kernel
theorem row244_generated : rootPair 244 = some rowPose244 :=
  pairFieldsMatchB_sound (by decide) row244_fields
theorem row244_source : sourceKey 244 ∈ geometry.profile (sourceOwner 244) := by decide +kernel
theorem row244_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 213 key0).FastValid geometry rowPose244 := by decide +kernel
theorem row244_illegal : ¬ geometry.LegalContact rowPose244 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row244_reject_checked)
theorem row244_classified : RowClassified 244 := by
  intro p generated legal
  have he : rowPose244 = p := Option.some.inj (row244_generated.symm.trans generated)
  subst p
  exact (row244_illegal legal).elim

def rowPose245 : Pose 7 := ⟨perm73, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row245_fields : pairFieldsMatchB 188160 facet0 facet214 key0 key245 rowPose245 = true := by decide +kernel
theorem row245_generated : rootPair 245 = some rowPose245 :=
  pairFieldsMatchB_sound (by decide) row245_fields
theorem row245_source : sourceKey 245 ∈ geometry.profile (sourceOwner 245) := by decide +kernel
theorem row245_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 214 key1).FastValid geometry rowPose245 := by decide +kernel
theorem row245_illegal : ¬ geometry.LegalContact rowPose245 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row245_reject_checked)
theorem row245_classified : RowClassified 245 := by
  intro p generated legal
  have he : rowPose245 = p := Option.some.inj (row245_generated.symm.trans generated)
  subst p
  exact (row245_illegal legal).elim

def rowPose246 : Pose 7 := ⟨perm87, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row246_fields : pairFieldsMatchB 188160 facet0 facet215 key0 key246 rowPose246 = true := by decide +kernel
theorem row246_generated : rootPair 246 = some rowPose246 :=
  pairFieldsMatchB_sound (by decide) row246_fields
theorem row246_source : sourceKey 246 ∈ geometry.profile (sourceOwner 246) := by decide +kernel
theorem row246_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 215 key0).FastValid geometry rowPose246 := by decide +kernel
theorem row246_illegal : ¬ geometry.LegalContact rowPose246 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row246_reject_checked)
theorem row246_classified : RowClassified 246 := by
  intro p generated legal
  have he : rowPose246 = p := Option.some.inj (row246_generated.symm.trans generated)
  subst p
  exact (row246_illegal legal).elim

def rowPose247 : Pose 7 := ⟨perm96, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row247_fields : pairFieldsMatchB 188160 facet0 facet216 key0 key247 rowPose247 = true := by decide +kernel
theorem row247_generated : rootPair 247 = some rowPose247 :=
  pairFieldsMatchB_sound (by decide) row247_fields
theorem row247_source : sourceKey 247 ∈ geometry.profile (sourceOwner 247) := by decide +kernel
theorem row247_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 216 key0).FastValid geometry rowPose247 := by decide +kernel
theorem row247_illegal : ¬ geometry.LegalContact rowPose247 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row247_reject_checked)
theorem row247_classified : RowClassified 247 := by
  intro p generated legal
  have he : rowPose247 = p := Option.some.inj (row247_generated.symm.trans generated)
  subst p
  exact (row247_illegal legal).elim

def rowPose248 : Pose 7 := ⟨perm10, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row248_fields : pairFieldsMatchB 188160 facet0 facet217 key0 key248 rowPose248 = true := by decide +kernel
theorem row248_generated : rootPair 248 = some rowPose248 :=
  pairFieldsMatchB_sound (by decide) row248_fields
theorem row248_source : sourceKey 248 ∈ geometry.profile (sourceOwner 248) := by decide +kernel
theorem row248_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 217 key1).FastValid geometry rowPose248 := by decide +kernel
theorem row248_illegal : ¬ geometry.LegalContact rowPose248 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row248_reject_checked)
theorem row248_classified : RowClassified 248 := by
  intro p generated legal
  have he : rowPose248 = p := Option.some.inj (row248_generated.symm.trans generated)
  subst p
  exact (row248_illegal legal).elim

def rowPose249 : Pose 7 := ⟨perm22, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row249_fields : pairFieldsMatchB 188160 facet0 facet218 key0 key249 rowPose249 = true := by decide +kernel
theorem row249_generated : rootPair 249 = some rowPose249 :=
  pairFieldsMatchB_sound (by decide) row249_fields
theorem row249_source : sourceKey 249 ∈ geometry.profile (sourceOwner 249) := by decide +kernel
theorem row249_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 218 key0).FastValid geometry rowPose249 := by decide +kernel
theorem row249_illegal : ¬ geometry.LegalContact rowPose249 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row249_reject_checked)
theorem row249_classified : RowClassified 249 := by
  intro p generated legal
  have he : rowPose249 = p := Option.some.inj (row249_generated.symm.trans generated)
  subst p
  exact (row249_illegal legal).elim

def rowPose250 : Pose 7 := ⟨perm37, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row250_fields : pairFieldsMatchB 188160 facet0 facet219 key0 key250 rowPose250 = true := by decide +kernel
theorem row250_generated : rootPair 250 = some rowPose250 :=
  pairFieldsMatchB_sound (by decide) row250_fields
theorem row250_source : sourceKey 250 ∈ geometry.profile (sourceOwner 250) := by decide +kernel
theorem row250_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 219 key1).FastValid geometry rowPose250 := by decide +kernel
theorem row250_illegal : ¬ geometry.LegalContact rowPose250 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row250_reject_checked)
theorem row250_classified : RowClassified 250 := by
  intro p generated legal
  have he : rowPose250 = p := Option.some.inj (row250_generated.symm.trans generated)
  subst p
  exact (row250_illegal legal).elim

def rowPose251 : Pose 7 := ⟨perm58, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row251_fields : pairFieldsMatchB 188160 facet0 facet220 key0 key251 rowPose251 = true := by decide +kernel
theorem row251_generated : rootPair 251 = some rowPose251 :=
  pairFieldsMatchB_sound (by decide) row251_fields
theorem row251_source : sourceKey 251 ∈ geometry.profile (sourceOwner 251) := by decide +kernel
theorem row251_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 220 key1).FastValid geometry rowPose251 := by decide +kernel
theorem row251_illegal : ¬ geometry.LegalContact rowPose251 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row251_reject_checked)
theorem row251_classified : RowClassified 251 := by
  intro p generated legal
  have he : rowPose251 = p := Option.some.inj (row251_generated.symm.trans generated)
  subst p
  exact (row251_illegal legal).elim

def rowPose252 : Pose 7 := ⟨perm74, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row252_fields : pairFieldsMatchB 188160 facet0 facet221 key0 key252 rowPose252 = true := by decide +kernel
theorem row252_generated : rootPair 252 = some rowPose252 :=
  pairFieldsMatchB_sound (by decide) row252_fields
theorem row252_source : sourceKey 252 ∈ geometry.profile (sourceOwner 252) := by decide +kernel
theorem row252_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 165 key8).FastValid geometry rowPose252 := by decide +kernel
theorem row252_illegal : ¬ geometry.LegalContact rowPose252 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row252_reject_checked)
theorem row252_classified : RowClassified 252 := by
  intro p generated legal
  have he : rowPose252 = p := Option.some.inj (row252_generated.symm.trans generated)
  subst p
  exact (row252_illegal legal).elim

def rowPose253 : Pose 7 := ⟨perm69, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row253_fields : pairFieldsMatchB 188160 facet0 facet221 key0 key253 rowPose253 = true := by decide +kernel
theorem row253_generated : rootPair 253 = some rowPose253 :=
  pairFieldsMatchB_sound (by decide) row253_fields
theorem row253_source : sourceKey 253 ∈ geometry.profile (sourceOwner 253) := by decide +kernel
theorem row253_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 221 key0).FastValid geometry rowPose253 := by decide +kernel
theorem row253_illegal : ¬ geometry.LegalContact rowPose253 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row253_reject_checked)
theorem row253_classified : RowClassified 253 := by
  intro p generated legal
  have he : rowPose253 = p := Option.some.inj (row253_generated.symm.trans generated)
  subst p
  exact (row253_illegal legal).elim

def rowPose254 : Pose 7 := ⟨perm87, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row254_fields : pairFieldsMatchB 188160 facet0 facet222 key0 key254 rowPose254 = true := by decide +kernel
theorem row254_generated : rootPair 254 = some rowPose254 :=
  pairFieldsMatchB_sound (by decide) row254_fields
theorem row254_source : sourceKey 254 ∈ geometry.profile (sourceOwner 254) := by decide +kernel
theorem row254_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 222 key0).FastValid geometry rowPose254 := by decide +kernel
theorem row254_illegal : ¬ geometry.LegalContact rowPose254 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row254_reject_checked)
theorem row254_classified : RowClassified 254 := by
  intro p generated legal
  have he : rowPose254 = p := Option.some.inj (row254_generated.symm.trans generated)
  subst p
  exact (row254_illegal legal).elim

def rowPose255 : Pose 7 := ⟨perm96, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row255_fields : pairFieldsMatchB 188160 facet0 facet223 key0 key255 rowPose255 = true := by decide +kernel
theorem row255_generated : rootPair 255 = some rowPose255 :=
  pairFieldsMatchB_sound (by decide) row255_fields
theorem row255_source : sourceKey 255 ∈ geometry.profile (sourceOwner 255) := by decide +kernel
theorem row255_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 223 key0).FastValid geometry rowPose255 := by decide +kernel
theorem row255_illegal : ¬ geometry.LegalContact rowPose255 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row255_reject_checked)
theorem row255_classified : RowClassified 255 := by
  intro p generated legal
  have he : rowPose255 = p := Option.some.inj (row255_generated.symm.trans generated)
  subst p
  exact (row255_illegal legal).elim

theorem chunk07_classified (i : Fin 32) : RowClassified ⟨224 + i.val, by omega⟩ := by
  fin_cases i
  · exact row224_classified
  · exact row225_classified
  · exact row226_classified
  · exact row227_classified
  · exact row228_classified
  · exact row229_classified
  · exact row230_classified
  · exact row231_classified
  · exact row232_classified
  · exact row233_classified
  · exact row234_classified
  · exact row235_classified
  · exact row236_classified
  · exact row237_classified
  · exact row238_classified
  · exact row239_classified
  · exact row240_classified
  · exact row241_classified
  · exact row242_classified
  · exact row243_classified
  · exact row244_classified
  · exact row245_classified
  · exact row246_classified
  · exact row247_classified
  · exact row248_classified
  · exact row249_classified
  · exact row250_classified
  · exact row251_classified
  · exact row252_classified
  · exact row253_classified
  · exact row254_classified
  · exact row255_classified

theorem chunk07_source (i : Fin 32) : sourceKey ⟨224 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨224 + i.val, by omega⟩) := by
  fin_cases i
  · exact row224_source
  · exact row225_source
  · exact row226_source
  · exact row227_source
  · exact row228_source
  · exact row229_source
  · exact row230_source
  · exact row231_source
  · exact row232_source
  · exact row233_source
  · exact row234_source
  · exact row235_source
  · exact row236_source
  · exact row237_source
  · exact row238_source
  · exact row239_source
  · exact row240_source
  · exact row241_source
  · exact row242_source
  · exact row243_source
  · exact row244_source
  · exact row245_source
  · exact row246_source
  · exact row247_source
  · exact row248_source
  · exact row249_source
  · exact row250_source
  · exact row251_source
  · exact row252_source
  · exact row253_source
  · exact row254_source
  · exact row255_source

#print axioms chunk07_classified
end SparseMonotiles.Contact.RootZeroPilot7
