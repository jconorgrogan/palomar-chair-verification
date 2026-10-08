module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose256 : Pose 7 := ⟨perm0, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row256_fields : pairFieldsMatchB 188160 facet0 facet224 key0 key256 rowPose256 = true := by decide +kernel
theorem row256_generated : rootPair 256 = some rowPose256 :=
  pairFieldsMatchB_sound (by decide) row256_fields
theorem row256_source : sourceKey 256 ∈ geometry.profile (sourceOwner 256) := by decide +kernel
theorem row256_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 224 key1).FastValid geometry rowPose256 := by decide +kernel
theorem row256_illegal : ¬ geometry.LegalContact rowPose256 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row256_reject_checked)
theorem row256_classified : RowClassified 256 := by
  intro p generated legal
  have he : rowPose256 = p := Option.some.inj (row256_generated.symm.trans generated)
  subst p
  exact (row256_illegal legal).elim

def rowPose257 : Pose 7 := ⟨perm21, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row257_fields : pairFieldsMatchB 188160 facet0 facet225 key0 key257 rowPose257 = true := by decide +kernel
theorem row257_generated : rootPair 257 = some rowPose257 :=
  pairFieldsMatchB_sound (by decide) row257_fields
theorem row257_source : sourceKey 257 ∈ geometry.profile (sourceOwner 257) := by decide +kernel
theorem row257_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 225 key0).FastValid geometry rowPose257 := by decide +kernel
theorem row257_illegal : ¬ geometry.LegalContact rowPose257 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row257_reject_checked)
theorem row257_classified : RowClassified 257 := by
  intro p generated legal
  have he : rowPose257 = p := Option.some.inj (row257_generated.symm.trans generated)
  subst p
  exact (row257_illegal legal).elim

def rowPose258 : Pose 7 := ⟨perm24, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row258_fields : pairFieldsMatchB 188160 facet0 facet225 key0 key258 rowPose258 = true := by decide +kernel
theorem row258_generated : rootPair 258 = some rowPose258 :=
  pairFieldsMatchB_sound (by decide) row258_fields
theorem row258_source : sourceKey 258 ∈ geometry.profile (sourceOwner 258) := by decide +kernel
theorem row258_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 675 key8).FastValid geometry rowPose258 := by decide +kernel
theorem row258_illegal : ¬ geometry.LegalContact rowPose258 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row258_reject_checked)
theorem row258_classified : RowClassified 258 := by
  intro p generated legal
  have he : rowPose258 = p := Option.some.inj (row258_generated.symm.trans generated)
  subst p
  exact (row258_illegal legal).elim

def rowPose259 : Pose 7 := ⟨perm37, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row259_fields : pairFieldsMatchB 188160 facet0 facet226 key0 key259 rowPose259 = true := by decide +kernel
theorem row259_generated : rootPair 259 = some rowPose259 :=
  pairFieldsMatchB_sound (by decide) row259_fields
theorem row259_source : sourceKey 259 ∈ geometry.profile (sourceOwner 259) := by decide +kernel
theorem row259_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 226 key0).FastValid geometry rowPose259 := by decide +kernel
theorem row259_illegal : ¬ geometry.LegalContact rowPose259 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row259_reject_checked)
theorem row259_classified : RowClassified 259 := by
  intro p generated legal
  have he : rowPose259 = p := Option.some.inj (row259_generated.symm.trans generated)
  subst p
  exact (row259_illegal legal).elim

def rowPose260 : Pose 7 := ⟨perm58, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row260_fields : pairFieldsMatchB 188160 facet0 facet227 key0 key260 rowPose260 = true := by decide +kernel
theorem row260_generated : rootPair 260 = some rowPose260 :=
  pairFieldsMatchB_sound (by decide) row260_fields
theorem row260_source : sourceKey 260 ∈ geometry.profile (sourceOwner 260) := by decide +kernel
theorem row260_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 227 key0).FastValid geometry rowPose260 := by decide +kernel
theorem row260_illegal : ¬ geometry.LegalContact rowPose260 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row260_reject_checked)
theorem row260_classified : RowClassified 260 := by
  intro p generated legal
  have he : rowPose260 = p := Option.some.inj (row260_generated.symm.trans generated)
  subst p
  exact (row260_illegal legal).elim

def rowPose261 : Pose 7 := ⟨perm71, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row261_fields : pairFieldsMatchB 188160 facet0 facet228 key0 key261 rowPose261 = true := by decide +kernel
theorem row261_generated : rootPair 261 = some rowPose261 :=
  pairFieldsMatchB_sound (by decide) row261_fields
theorem row261_source : sourceKey 261 ∈ geometry.profile (sourceOwner 261) := by decide +kernel
theorem row261_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 228 key1).FastValid geometry rowPose261 := by decide +kernel
theorem row261_illegal : ¬ geometry.LegalContact rowPose261 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row261_reject_checked)
theorem row261_classified : RowClassified 261 := by
  intro p generated legal
  have he : rowPose261 = p := Option.some.inj (row261_generated.symm.trans generated)
  subst p
  exact (row261_illegal legal).elim

def rowPose262 : Pose 7 := ⟨perm95, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row262_fields : pairFieldsMatchB 188160 facet0 facet229 key0 key262 rowPose262 = true := by decide +kernel
theorem row262_generated : rootPair 262 = some rowPose262 :=
  pairFieldsMatchB_sound (by decide) row262_fields
theorem row262_source : sourceKey 262 ∈ geometry.profile (sourceOwner 262) := by decide +kernel
theorem row262_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 229 key0).FastValid geometry rowPose262 := by decide +kernel
theorem row262_illegal : ¬ geometry.LegalContact rowPose262 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row262_reject_checked)
theorem row262_classified : RowClassified 262 := by
  intro p generated legal
  have he : rowPose262 = p := Option.some.inj (row262_generated.symm.trans generated)
  subst p
  exact (row262_illegal legal).elim

def rowPose263 : Pose 7 := ⟨perm111, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row263_fields : pairFieldsMatchB 188160 facet0 facet230 key0 key263 rowPose263 = true := by decide +kernel
theorem row263_generated : rootPair 263 = some rowPose263 :=
  pairFieldsMatchB_sound (by decide) row263_fields
theorem row263_source : sourceKey 263 ∈ geometry.profile (sourceOwner 263) := by decide +kernel
theorem row263_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 230 key1).FastValid geometry rowPose263 := by decide +kernel
theorem row263_illegal : ¬ geometry.LegalContact rowPose263 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row263_reject_checked)
theorem row263_classified : RowClassified 263 := by
  intro p generated legal
  have he : rowPose263 = p := Option.some.inj (row263_generated.symm.trans generated)
  subst p
  exact (row263_illegal legal).elim

def rowPose264 : Pose 7 := ⟨perm0, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row264_fields : pairFieldsMatchB 188160 facet0 facet231 key0 key264 rowPose264 = true := by decide +kernel
theorem row264_generated : rootPair 264 = some rowPose264 :=
  pairFieldsMatchB_sound (by decide) row264_fields
theorem row264_source : sourceKey 264 ∈ geometry.profile (sourceOwner 264) := by decide +kernel
theorem row264_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 231 key0).FastValid geometry rowPose264 := by decide +kernel
theorem row264_illegal : ¬ geometry.LegalContact rowPose264 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row264_reject_checked)
theorem row264_classified : RowClassified 264 := by
  intro p generated legal
  have he : rowPose264 = p := Option.some.inj (row264_generated.symm.trans generated)
  subst p
  exact (row264_illegal legal).elim

def rowPose265 : Pose 7 := ⟨perm15, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row265_fields : pairFieldsMatchB 188160 facet0 facet231 key0 key265 rowPose265 = true := by decide +kernel
theorem row265_generated : rootPair 265 = some rowPose265 :=
  pairFieldsMatchB_sound (by decide) row265_fields
theorem row265_source : sourceKey 265 ∈ geometry.profile (sourceOwner 265) := by decide +kernel
theorem row265_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 7 key8).FastValid geometry rowPose265 := by decide +kernel
theorem row265_illegal : ¬ geometry.LegalContact rowPose265 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row265_reject_checked)
theorem row265_classified : RowClassified 265 := by
  intro p generated legal
  have he : rowPose265 = p := Option.some.inj (row265_generated.symm.trans generated)
  subst p
  exact (row265_illegal legal).elim

def rowPose266 : Pose 7 := ⟨perm21, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row266_fields : pairFieldsMatchB 188160 facet0 facet232 key0 key266 rowPose266 = true := by decide +kernel
theorem row266_generated : rootPair 266 = some rowPose266 :=
  pairFieldsMatchB_sound (by decide) row266_fields
theorem row266_source : sourceKey 266 ∈ geometry.profile (sourceOwner 266) := by decide +kernel
theorem row266_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 232 key1).FastValid geometry rowPose266 := by decide +kernel
theorem row266_illegal : ¬ geometry.LegalContact rowPose266 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row266_reject_checked)
theorem row266_classified : RowClassified 266 := by
  intro p generated legal
  have he : rowPose266 = p := Option.some.inj (row266_generated.symm.trans generated)
  subst p
  exact (row266_illegal legal).elim

def rowPose267 : Pose 7 := ⟨perm42, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row267_fields : pairFieldsMatchB 188160 facet0 facet233 key0 key267 rowPose267 = true := by decide +kernel
theorem row267_generated : rootPair 267 = some rowPose267 :=
  pairFieldsMatchB_sound (by decide) row267_fields
theorem row267_source : sourceKey 267 ∈ geometry.profile (sourceOwner 267) := by decide +kernel
theorem row267_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 233 key1).FastValid geometry rowPose267 := by decide +kernel
theorem row267_illegal : ¬ geometry.LegalContact rowPose267 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row267_reject_checked)
theorem row267_classified : RowClassified 267 := by
  intro p generated legal
  have he : rowPose267 = p := Option.some.inj (row267_generated.symm.trans generated)
  subst p
  exact (row267_illegal legal).elim

def rowPose268 : Pose 7 := ⟨perm55, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row268_fields : pairFieldsMatchB 188160 facet0 facet234 key0 key268 rowPose268 = true := by decide +kernel
theorem row268_generated : rootPair 268 = some rowPose268 :=
  pairFieldsMatchB_sound (by decide) row268_fields
theorem row268_source : sourceKey 268 ∈ geometry.profile (sourceOwner 268) := by decide +kernel
theorem row268_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 234 key0).FastValid geometry rowPose268 := by decide +kernel
theorem row268_illegal : ¬ geometry.LegalContact rowPose268 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row268_reject_checked)
theorem row268_classified : RowClassified 268 := by
  intro p generated legal
  have he : rowPose268 = p := Option.some.inj (row268_generated.symm.trans generated)
  subst p
  exact (row268_illegal legal).elim

def rowPose269 : Pose 7 := ⟨perm73, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row269_fields : pairFieldsMatchB 188160 facet0 facet235 key0 key269 rowPose269 = true := by decide +kernel
theorem row269_generated : rootPair 269 = some rowPose269 :=
  pairFieldsMatchB_sound (by decide) row269_fields
theorem row269_source : sourceKey 269 ∈ geometry.profile (sourceOwner 269) := by decide +kernel
theorem row269_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 235 key1).FastValid geometry rowPose269 := by decide +kernel
theorem row269_illegal : ¬ geometry.LegalContact rowPose269 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row269_reject_checked)
theorem row269_classified : RowClassified 269 := by
  intro p generated legal
  have he : rowPose269 = p := Option.some.inj (row269_generated.symm.trans generated)
  subst p
  exact (row269_illegal legal).elim

def rowPose270 : Pose 7 := ⟨perm87, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row270_fields : pairFieldsMatchB 188160 facet0 facet236 key0 key270 rowPose270 = true := by decide +kernel
theorem row270_generated : rootPair 270 = some rowPose270 :=
  pairFieldsMatchB_sound (by decide) row270_fields
theorem row270_source : sourceKey 270 ∈ geometry.profile (sourceOwner 270) := by decide +kernel
theorem row270_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 236 key0).FastValid geometry rowPose270 := by decide +kernel
theorem row270_illegal : ¬ geometry.LegalContact rowPose270 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row270_reject_checked)
theorem row270_classified : RowClassified 270 := by
  intro p generated legal
  have he : rowPose270 = p := Option.some.inj (row270_generated.symm.trans generated)
  subst p
  exact (row270_illegal legal).elim

def rowPose271 : Pose 7 := ⟨perm96, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row271_fields : pairFieldsMatchB 188160 facet0 facet237 key0 key271 rowPose271 = true := by decide +kernel
theorem row271_generated : rootPair 271 = some rowPose271 :=
  pairFieldsMatchB_sound (by decide) row271_fields
theorem row271_source : sourceKey 271 ∈ geometry.profile (sourceOwner 271) := by decide +kernel
theorem row271_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 237 key0).FastValid geometry rowPose271 := by decide +kernel
theorem row271_illegal : ¬ geometry.LegalContact rowPose271 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row271_reject_checked)
theorem row271_classified : RowClassified 271 := by
  intro p generated legal
  have he : rowPose271 = p := Option.some.inj (row271_generated.symm.trans generated)
  subst p
  exact (row271_illegal legal).elim

def rowPose272 : Pose 7 := ⟨perm5, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row272_fields : pairFieldsMatchB 188160 facet0 facet238 key0 key272 rowPose272 = true := by decide +kernel
theorem row272_generated : rootPair 272 = some rowPose272 :=
  pairFieldsMatchB_sound (by decide) row272_fields
theorem row272_source : sourceKey 272 ∈ geometry.profile (sourceOwner 272) := by decide +kernel
theorem row272_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 238 key1).FastValid geometry rowPose272 := by decide +kernel
theorem row272_illegal : ¬ geometry.LegalContact rowPose272 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row272_reject_checked)
theorem row272_classified : RowClassified 272 := by
  intro p generated legal
  have he : rowPose272 = p := Option.some.inj (row272_generated.symm.trans generated)
  subst p
  exact (row272_illegal legal).elim

def rowPose273 : Pose 7 := ⟨perm21, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row273_fields : pairFieldsMatchB 188160 facet0 facet239 key0 key273 rowPose273 = true := by decide +kernel
theorem row273_generated : rootPair 273 = some rowPose273 :=
  pairFieldsMatchB_sound (by decide) row273_fields
theorem row273_source : sourceKey 273 ∈ geometry.profile (sourceOwner 273) := by decide +kernel
theorem row273_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 239 key0).FastValid geometry rowPose273 := by decide +kernel
theorem row273_illegal : ¬ geometry.LegalContact rowPose273 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row273_reject_checked)
theorem row273_classified : RowClassified 273 := by
  intro p generated legal
  have he : rowPose273 = p := Option.some.inj (row273_generated.symm.trans generated)
  subst p
  exact (row273_illegal legal).elim

def rowPose274 : Pose 7 := ⟨perm42, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row274_fields : pairFieldsMatchB 188160 facet0 facet240 key0 key274 rowPose274 = true := by decide +kernel
theorem row274_generated : rootPair 274 = some rowPose274 :=
  pairFieldsMatchB_sound (by decide) row274_fields
theorem row274_source : sourceKey 274 ∈ geometry.profile (sourceOwner 274) := by decide +kernel
theorem row274_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 240 key0).FastValid geometry rowPose274 := by decide +kernel
theorem row274_illegal : ¬ geometry.LegalContact rowPose274 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row274_reject_checked)
theorem row274_classified : RowClassified 274 := by
  intro p generated legal
  have he : rowPose274 = p := Option.some.inj (row274_generated.symm.trans generated)
  subst p
  exact (row274_illegal legal).elim

def rowPose275 : Pose 7 := ⟨perm53, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row275_fields : pairFieldsMatchB 188160 facet0 facet241 key0 key275 rowPose275 = true := by decide +kernel
theorem row275_generated : rootPair 275 = some rowPose275 :=
  pairFieldsMatchB_sound (by decide) row275_fields
theorem row275_source : sourceKey 275 ∈ geometry.profile (sourceOwner 275) := by decide +kernel
theorem row275_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 269 key8).FastValid geometry rowPose275 := by decide +kernel
theorem row275_illegal : ¬ geometry.LegalContact rowPose275 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row275_reject_checked)
theorem row275_classified : RowClassified 275 := by
  intro p generated legal
  have he : rowPose275 = p := Option.some.inj (row275_generated.symm.trans generated)
  subst p
  exact (row275_illegal legal).elim

def rowPose276 : Pose 7 := ⟨perm58, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row276_fields : pairFieldsMatchB 188160 facet0 facet241 key0 key276 rowPose276 = true := by decide +kernel
theorem row276_generated : rootPair 276 = some rowPose276 :=
  pairFieldsMatchB_sound (by decide) row276_fields
theorem row276_source : sourceKey 276 ∈ geometry.profile (sourceOwner 276) := by decide +kernel
theorem row276_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 241 key0).FastValid geometry rowPose276 := by decide +kernel
theorem row276_illegal : ¬ geometry.LegalContact rowPose276 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row276_reject_checked)
theorem row276_classified : RowClassified 276 := by
  intro p generated legal
  have he : rowPose276 = p := Option.some.inj (row276_generated.symm.trans generated)
  subst p
  exact (row276_illegal legal).elim

def rowPose277 : Pose 7 := ⟨perm69, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row277_fields : pairFieldsMatchB 188160 facet0 facet242 key0 key277 rowPose277 = true := by decide +kernel
theorem row277_generated : rootPair 277 = some rowPose277 :=
  pairFieldsMatchB_sound (by decide) row277_fields
theorem row277_source : sourceKey 277 ∈ geometry.profile (sourceOwner 277) := by decide +kernel
theorem row277_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 242 key1).FastValid geometry rowPose277 := by decide +kernel
theorem row277_illegal : ¬ geometry.LegalContact rowPose277 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row277_reject_checked)
theorem row277_classified : RowClassified 277 := by
  intro p generated legal
  have he : rowPose277 = p := Option.some.inj (row277_generated.symm.trans generated)
  subst p
  exact (row277_illegal legal).elim

def rowPose278 : Pose 7 := ⟨perm90, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row278_fields : pairFieldsMatchB 188160 facet0 facet243 key0 key278 rowPose278 = true := by decide +kernel
theorem row278_generated : rootPair 278 = some rowPose278 :=
  pairFieldsMatchB_sound (by decide) row278_fields
theorem row278_source : sourceKey 278 ∈ geometry.profile (sourceOwner 278) := by decide +kernel
theorem row278_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 243 key1).FastValid geometry rowPose278 := by decide +kernel
theorem row278_illegal : ¬ geometry.LegalContact rowPose278 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row278_reject_checked)
theorem row278_classified : RowClassified 278 := by
  intro p generated legal
  have he : rowPose278 = p := Option.some.inj (row278_generated.symm.trans generated)
  subst p
  exact (row278_illegal legal).elim

def rowPose279 : Pose 7 := ⟨perm106, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row279_fields : pairFieldsMatchB 188160 facet0 facet244 key0 key279 rowPose279 = true := by decide +kernel
theorem row279_generated : rootPair 279 = some rowPose279 :=
  pairFieldsMatchB_sound (by decide) row279_fields
theorem row279_source : sourceKey 279 ∈ geometry.profile (sourceOwner 279) := by decide +kernel
theorem row279_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 244 key0).FastValid geometry rowPose279 := by decide +kernel
theorem row279_illegal : ¬ geometry.LegalContact rowPose279 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row279_reject_checked)
theorem row279_classified : RowClassified 279 := by
  intro p generated legal
  have he : rowPose279 = p := Option.some.inj (row279_generated.symm.trans generated)
  subst p
  exact (row279_illegal legal).elim

def rowPose280 : Pose 7 := ⟨perm10, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row280_fields : pairFieldsMatchB 188160 facet0 facet245 key0 key280 rowPose280 = true := by decide +kernel
theorem row280_generated : rootPair 280 = some rowPose280 :=
  pairFieldsMatchB_sound (by decide) row280_fields
theorem row280_source : sourceKey 280 ∈ geometry.profile (sourceOwner 280) := by decide +kernel
theorem row280_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 245 key1).FastValid geometry rowPose280 := by decide +kernel
theorem row280_illegal : ¬ geometry.LegalContact rowPose280 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row280_reject_checked)
theorem row280_classified : RowClassified 280 := by
  intro p generated legal
  have he : rowPose280 = p := Option.some.inj (row280_generated.symm.trans generated)
  subst p
  exact (row280_illegal legal).elim

def rowPose281 : Pose 7 := ⟨perm22, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row281_fields : pairFieldsMatchB 188160 facet0 facet246 key0 key281 rowPose281 = true := by decide +kernel
theorem row281_generated : rootPair 281 = some rowPose281 :=
  pairFieldsMatchB_sound (by decide) row281_fields
theorem row281_source : sourceKey 281 ∈ geometry.profile (sourceOwner 281) := by decide +kernel
theorem row281_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 246 key0).FastValid geometry rowPose281 := by decide +kernel
theorem row281_illegal : ¬ geometry.LegalContact rowPose281 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row281_reject_checked)
theorem row281_classified : RowClassified 281 := by
  intro p generated legal
  have he : rowPose281 = p := Option.some.inj (row281_generated.symm.trans generated)
  subst p
  exact (row281_illegal legal).elim

def rowPose282 : Pose 7 := ⟨perm37, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row282_fields : pairFieldsMatchB 188160 facet0 facet247 key0 key282 rowPose282 = true := by decide +kernel
theorem row282_generated : rootPair 282 = some rowPose282 :=
  pairFieldsMatchB_sound (by decide) row282_fields
theorem row282_source : sourceKey 282 ∈ geometry.profile (sourceOwner 282) := by decide +kernel
theorem row282_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 247 key1).FastValid geometry rowPose282 := by decide +kernel
theorem row282_illegal : ¬ geometry.LegalContact rowPose282 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row282_reject_checked)
theorem row282_classified : RowClassified 282 := by
  intro p generated legal
  have he : rowPose282 = p := Option.some.inj (row282_generated.symm.trans generated)
  subst p
  exact (row282_illegal legal).elim

def rowPose283 : Pose 7 := ⟨perm58, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row283_fields : pairFieldsMatchB 188160 facet0 facet248 key0 key283 rowPose283 = true := by decide +kernel
theorem row283_generated : rootPair 283 = some rowPose283 :=
  pairFieldsMatchB_sound (by decide) row283_fields
theorem row283_source : sourceKey 283 ∈ geometry.profile (sourceOwner 283) := by decide +kernel
theorem row283_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 248 key1).FastValid geometry rowPose283 := by decide +kernel
theorem row283_illegal : ¬ geometry.LegalContact rowPose283 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row283_reject_checked)
theorem row283_classified : RowClassified 283 := by
  intro p generated legal
  have he : rowPose283 = p := Option.some.inj (row283_generated.symm.trans generated)
  subst p
  exact (row283_illegal legal).elim

def rowPose284 : Pose 7 := ⟨perm74, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row284_fields : pairFieldsMatchB 188160 facet0 facet249 key0 key284 rowPose284 = true := by decide +kernel
theorem row284_generated : rootPair 284 = some rowPose284 :=
  pairFieldsMatchB_sound (by decide) row284_fields
theorem row284_source : sourceKey 284 ∈ geometry.profile (sourceOwner 284) := by decide +kernel
theorem row284_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 305 key8).FastValid geometry rowPose284 := by decide +kernel
theorem row284_illegal : ¬ geometry.LegalContact rowPose284 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row284_reject_checked)
theorem row284_classified : RowClassified 284 := by
  intro p generated legal
  have he : rowPose284 = p := Option.some.inj (row284_generated.symm.trans generated)
  subst p
  exact (row284_illegal legal).elim

def rowPose285 : Pose 7 := ⟨perm69, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row285_fields : pairFieldsMatchB 188160 facet0 facet249 key0 key285 rowPose285 = true := by decide +kernel
theorem row285_generated : rootPair 285 = some rowPose285 :=
  pairFieldsMatchB_sound (by decide) row285_fields
theorem row285_source : sourceKey 285 ∈ geometry.profile (sourceOwner 285) := by decide +kernel
theorem row285_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 249 key0).FastValid geometry rowPose285 := by decide +kernel
theorem row285_illegal : ¬ geometry.LegalContact rowPose285 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row285_reject_checked)
theorem row285_classified : RowClassified 285 := by
  intro p generated legal
  have he : rowPose285 = p := Option.some.inj (row285_generated.symm.trans generated)
  subst p
  exact (row285_illegal legal).elim

def rowPose286 : Pose 7 := ⟨perm87, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row286_fields : pairFieldsMatchB 188160 facet0 facet250 key0 key286 rowPose286 = true := by decide +kernel
theorem row286_generated : rootPair 286 = some rowPose286 :=
  pairFieldsMatchB_sound (by decide) row286_fields
theorem row286_source : sourceKey 286 ∈ geometry.profile (sourceOwner 286) := by decide +kernel
theorem row286_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 250 key0).FastValid geometry rowPose286 := by decide +kernel
theorem row286_illegal : ¬ geometry.LegalContact rowPose286 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row286_reject_checked)
theorem row286_classified : RowClassified 286 := by
  intro p generated legal
  have he : rowPose286 = p := Option.some.inj (row286_generated.symm.trans generated)
  subst p
  exact (row286_illegal legal).elim

def rowPose287 : Pose 7 := ⟨perm96, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row287_fields : pairFieldsMatchB 188160 facet0 facet251 key0 key287 rowPose287 = true := by decide +kernel
theorem row287_generated : rootPair 287 = some rowPose287 :=
  pairFieldsMatchB_sound (by decide) row287_fields
theorem row287_source : sourceKey 287 ∈ geometry.profile (sourceOwner 287) := by decide +kernel
theorem row287_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 251 key0).FastValid geometry rowPose287 := by decide +kernel
theorem row287_illegal : ¬ geometry.LegalContact rowPose287 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row287_reject_checked)
theorem row287_classified : RowClassified 287 := by
  intro p generated legal
  have he : rowPose287 = p := Option.some.inj (row287_generated.symm.trans generated)
  subst p
  exact (row287_illegal legal).elim

theorem chunk08_classified (i : Fin 32) : RowClassified ⟨256 + i.val, by omega⟩ := by
  fin_cases i
  · exact row256_classified
  · exact row257_classified
  · exact row258_classified
  · exact row259_classified
  · exact row260_classified
  · exact row261_classified
  · exact row262_classified
  · exact row263_classified
  · exact row264_classified
  · exact row265_classified
  · exact row266_classified
  · exact row267_classified
  · exact row268_classified
  · exact row269_classified
  · exact row270_classified
  · exact row271_classified
  · exact row272_classified
  · exact row273_classified
  · exact row274_classified
  · exact row275_classified
  · exact row276_classified
  · exact row277_classified
  · exact row278_classified
  · exact row279_classified
  · exact row280_classified
  · exact row281_classified
  · exact row282_classified
  · exact row283_classified
  · exact row284_classified
  · exact row285_classified
  · exact row286_classified
  · exact row287_classified

theorem chunk08_source (i : Fin 32) : sourceKey ⟨256 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨256 + i.val, by omega⟩) := by
  fin_cases i
  · exact row256_source
  · exact row257_source
  · exact row258_source
  · exact row259_source
  · exact row260_source
  · exact row261_source
  · exact row262_source
  · exact row263_source
  · exact row264_source
  · exact row265_source
  · exact row266_source
  · exact row267_source
  · exact row268_source
  · exact row269_source
  · exact row270_source
  · exact row271_source
  · exact row272_source
  · exact row273_source
  · exact row274_source
  · exact row275_source
  · exact row276_source
  · exact row277_source
  · exact row278_source
  · exact row279_source
  · exact row280_source
  · exact row281_source
  · exact row282_source
  · exact row283_source
  · exact row284_source
  · exact row285_source
  · exact row286_source
  · exact row287_source

#print axioms chunk08_classified
end SparseMonotiles.Contact.RootZeroPilot7
