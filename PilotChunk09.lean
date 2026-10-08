module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose288 : Pose 7 := ⟨perm15, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row288_fields : pairFieldsMatchB 188160 facet0 facet252 key0 key288 rowPose288 = true := by decide +kernel
theorem row288_generated : rootPair 288 = some rowPose288 :=
  pairFieldsMatchB_sound (by decide) row288_fields
theorem row288_source : sourceKey 288 ∈ geometry.profile (sourceOwner 288) := by decide +kernel
theorem row288_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 252 key1).FastValid geometry rowPose288 := by decide +kernel
theorem row288_illegal : ¬ geometry.LegalContact rowPose288 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row288_reject_checked)
theorem row288_classified : RowClassified 288 := by
  intro p generated legal
  have he : rowPose288 = p := Option.some.inj (row288_generated.symm.trans generated)
  subst p
  exact (row288_illegal legal).elim

def rowPose289 : Pose 7 := ⟨perm24, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row289_fields : pairFieldsMatchB 188160 facet0 facet253 key0 key289 rowPose289 = true := by decide +kernel
theorem row289_generated : rootPair 289 = some rowPose289 :=
  pairFieldsMatchB_sound (by decide) row289_fields
theorem row289_source : sourceKey 289 ∈ geometry.profile (sourceOwner 289) := by decide +kernel
theorem row289_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 253 key1).FastValid geometry rowPose289 := by decide +kernel
theorem row289_illegal : ¬ geometry.LegalContact rowPose289 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row289_reject_checked)
theorem row289_classified : RowClassified 289 := by
  intro p generated legal
  have he : rowPose289 = p := Option.some.inj (row289_generated.symm.trans generated)
  subst p
  exact (row289_illegal legal).elim

def rowPose290 : Pose 7 := ⟨perm38, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row290_fields : pairFieldsMatchB 188160 facet0 facet254 key0 key290 rowPose290 = true := by decide +kernel
theorem row290_generated : rootPair 290 = some rowPose290 :=
  pairFieldsMatchB_sound (by decide) row290_fields
theorem row290_source : sourceKey 290 ∈ geometry.profile (sourceOwner 290) := by decide +kernel
theorem row290_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 254 key0).FastValid geometry rowPose290 := by decide +kernel
theorem row290_illegal : ¬ geometry.LegalContact rowPose290 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row290_reject_checked)
theorem row290_classified : RowClassified 290 := by
  intro p generated legal
  have he : rowPose290 = p := Option.some.inj (row290_generated.symm.trans generated)
  subst p
  exact (row290_illegal legal).elim

def rowPose291 : Pose 7 := ⟨perm56, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row291_fields : pairFieldsMatchB 188160 facet0 facet255 key0 key291 rowPose291 = true := by decide +kernel
theorem row291_generated : rootPair 291 = some rowPose291 :=
  pairFieldsMatchB_sound (by decide) row291_fields
theorem row291_source : sourceKey 291 ∈ geometry.profile (sourceOwner 291) := by decide +kernel
theorem row291_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 255 key1).FastValid geometry rowPose291 := by decide +kernel
theorem row291_illegal : ¬ geometry.LegalContact rowPose291 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row291_reject_checked)
theorem row291_classified : RowClassified 291 := by
  intro p generated legal
  have he : rowPose291 = p := Option.some.inj (row291_generated.symm.trans generated)
  subst p
  exact (row291_illegal legal).elim

def rowPose292 : Pose 7 := ⟨perm69, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row292_fields : pairFieldsMatchB 188160 facet0 facet256 key0 key292 rowPose292 = true := by decide +kernel
theorem row292_generated : rootPair 292 = some rowPose292 :=
  pairFieldsMatchB_sound (by decide) row292_fields
theorem row292_source : sourceKey 292 ∈ geometry.profile (sourceOwner 292) := by decide +kernel
theorem row292_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 256 key0).FastValid geometry rowPose292 := by decide +kernel
theorem row292_illegal : ¬ geometry.LegalContact rowPose292 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row292_reject_checked)
theorem row292_classified : RowClassified 292 := by
  intro p generated legal
  have he : rowPose292 = p := Option.some.inj (row292_generated.symm.trans generated)
  subst p
  exact (row292_illegal legal).elim

def rowPose293 : Pose 7 := ⟨perm90, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row293_fields : pairFieldsMatchB 188160 facet0 facet257 key0 key293 rowPose293 = true := by decide +kernel
theorem row293_generated : rootPair 293 = some rowPose293 :=
  pairFieldsMatchB_sound (by decide) row293_fields
theorem row293_source : sourceKey 293 ∈ geometry.profile (sourceOwner 293) := by decide +kernel
theorem row293_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 257 key0).FastValid geometry rowPose293 := by decide +kernel
theorem row293_illegal : ¬ geometry.LegalContact rowPose293 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row293_reject_checked)
theorem row293_classified : RowClassified 293 := by
  intro p generated legal
  have he : rowPose293 = p := Option.some.inj (row293_generated.symm.trans generated)
  subst p
  exact (row293_illegal legal).elim

def rowPose294 : Pose 7 := ⟨perm96, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row294_fields : pairFieldsMatchB 188160 facet0 facet258 key0 key294 rowPose294 = true := by decide +kernel
theorem row294_generated : rootPair 294 = some rowPose294 :=
  pairFieldsMatchB_sound (by decide) row294_fields
theorem row294_source : sourceKey 294 ∈ geometry.profile (sourceOwner 294) := by decide +kernel
theorem row294_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 258 key0).FastValid geometry rowPose294 := by decide +kernel
theorem row294_illegal : ¬ geometry.LegalContact rowPose294 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row294_reject_checked)
theorem row294_classified : RowClassified 294 := by
  intro p generated legal
  have he : rowPose294 = p := Option.some.inj (row294_generated.symm.trans generated)
  subst p
  exact (row294_illegal legal).elim

def rowPose295 : Pose 7 := ⟨perm111, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row295_fields : pairFieldsMatchB 188160 facet0 facet258 key0 key295 rowPose295 = true := by decide +kernel
theorem row295_generated : rootPair 295 = some rowPose295 :=
  pairFieldsMatchB_sound (by decide) row295_fields
theorem row295_source : sourceKey 295 ∈ geometry.profile (sourceOwner 295) := by decide +kernel
theorem row295_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 708 key8).FastValid geometry rowPose295 := by decide +kernel
theorem row295_illegal : ¬ geometry.LegalContact rowPose295 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row295_reject_checked)
theorem row295_classified : RowClassified 295 := by
  intro p generated legal
  have he : rowPose295 = p := Option.some.inj (row295_generated.symm.trans generated)
  subst p
  exact (row295_illegal legal).elim

def rowPose296 : Pose 7 := ⟨perm15, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row296_fields : pairFieldsMatchB 188160 facet0 facet259 key0 key296 rowPose296 = true := by decide +kernel
theorem row296_generated : rootPair 296 = some rowPose296 :=
  pairFieldsMatchB_sound (by decide) row296_fields
theorem row296_source : sourceKey 296 ∈ geometry.profile (sourceOwner 296) := by decide +kernel
theorem row296_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 259 key0).FastValid geometry rowPose296 := by decide +kernel
theorem row296_illegal : ¬ geometry.LegalContact rowPose296 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row296_reject_checked)
theorem row296_classified : RowClassified 296 := by
  intro p generated legal
  have he : rowPose296 = p := Option.some.inj (row296_generated.symm.trans generated)
  subst p
  exact (row296_illegal legal).elim

def rowPose297 : Pose 7 := ⟨perm24, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row297_fields : pairFieldsMatchB 188160 facet0 facet260 key0 key297 rowPose297 = true := by decide +kernel
theorem row297_generated : rootPair 297 = some rowPose297 :=
  pairFieldsMatchB_sound (by decide) row297_fields
theorem row297_source : sourceKey 297 ∈ geometry.profile (sourceOwner 297) := by decide +kernel
theorem row297_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 260 key0).FastValid geometry rowPose297 := by decide +kernel
theorem row297_illegal : ¬ geometry.LegalContact rowPose297 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row297_reject_checked)
theorem row297_classified : RowClassified 297 := by
  intro p generated legal
  have he : rowPose297 = p := Option.some.inj (row297_generated.symm.trans generated)
  subst p
  exact (row297_illegal legal).elim

def rowPose298 : Pose 7 := ⟨perm38, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row298_fields : pairFieldsMatchB 188160 facet0 facet261 key0 key298 rowPose298 = true := by decide +kernel
theorem row298_generated : rootPair 298 = some rowPose298 :=
  pairFieldsMatchB_sound (by decide) row298_fields
theorem row298_source : sourceKey 298 ∈ geometry.profile (sourceOwner 298) := by decide +kernel
theorem row298_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 261 key1).FastValid geometry rowPose298 := by decide +kernel
theorem row298_illegal : ¬ geometry.LegalContact rowPose298 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row298_reject_checked)
theorem row298_classified : RowClassified 298 := by
  intro p generated legal
  have he : rowPose298 = p := Option.some.inj (row298_generated.symm.trans generated)
  subst p
  exact (row298_illegal legal).elim

def rowPose299 : Pose 7 := ⟨perm56, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row299_fields : pairFieldsMatchB 188160 facet0 facet262 key0 key299 rowPose299 = true := by decide +kernel
theorem row299_generated : rootPair 299 = some rowPose299 :=
  pairFieldsMatchB_sound (by decide) row299_fields
theorem row299_source : sourceKey 299 ∈ geometry.profile (sourceOwner 299) := by decide +kernel
theorem row299_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 262 key0).FastValid geometry rowPose299 := by decide +kernel
theorem row299_illegal : ¬ geometry.LegalContact rowPose299 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row299_reject_checked)
theorem row299_classified : RowClassified 299 := by
  intro p generated legal
  have he : rowPose299 = p := Option.some.inj (row299_generated.symm.trans generated)
  subst p
  exact (row299_illegal legal).elim

def rowPose300 : Pose 7 := ⟨perm69, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row300_fields : pairFieldsMatchB 188160 facet0 facet263 key0 key300 rowPose300 = true := by decide +kernel
theorem row300_generated : rootPair 300 = some rowPose300 :=
  pairFieldsMatchB_sound (by decide) row300_fields
theorem row300_source : sourceKey 300 ∈ geometry.profile (sourceOwner 300) := by decide +kernel
theorem row300_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 263 key1).FastValid geometry rowPose300 := by decide +kernel
theorem row300_illegal : ¬ geometry.LegalContact rowPose300 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row300_reject_checked)
theorem row300_classified : RowClassified 300 := by
  intro p generated legal
  have he : rowPose300 = p := Option.some.inj (row300_generated.symm.trans generated)
  subst p
  exact (row300_illegal legal).elim

def rowPose301 : Pose 7 := ⟨perm90, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row301_fields : pairFieldsMatchB 188160 facet0 facet264 key0 key301 rowPose301 = true := by decide +kernel
theorem row301_generated : rootPair 301 = some rowPose301 :=
  pairFieldsMatchB_sound (by decide) row301_fields
theorem row301_source : sourceKey 301 ∈ geometry.profile (sourceOwner 301) := by decide +kernel
theorem row301_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 264 key1).FastValid geometry rowPose301 := by decide +kernel
theorem row301_illegal : ¬ geometry.LegalContact rowPose301 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row301_reject_checked)
theorem row301_classified : RowClassified 301 := by
  intro p generated legal
  have he : rowPose301 = p := Option.some.inj (row301_generated.symm.trans generated)
  subst p
  exact (row301_illegal legal).elim

def rowPose302 : Pose 7 := ⟨perm96, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row302_fields : pairFieldsMatchB 188160 facet0 facet265 key0 key302 rowPose302 = true := by decide +kernel
theorem row302_generated : rootPair 302 = some rowPose302 :=
  pairFieldsMatchB_sound (by decide) row302_fields
theorem row302_source : sourceKey 302 ∈ geometry.profile (sourceOwner 302) := by decide +kernel
theorem row302_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 279 key8).FastValid geometry rowPose302 := by decide +kernel
theorem row302_illegal : ¬ geometry.LegalContact rowPose302 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row302_reject_checked)
theorem row302_classified : RowClassified 302 := by
  intro p generated legal
  have he : rowPose302 = p := Option.some.inj (row302_generated.symm.trans generated)
  subst p
  exact (row302_illegal legal).elim

def rowPose303 : Pose 7 := ⟨perm111, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row303_fields : pairFieldsMatchB 188160 facet0 facet265 key0 key303 rowPose303 = true := by decide +kernel
theorem row303_generated : rootPair 303 = some rowPose303 :=
  pairFieldsMatchB_sound (by decide) row303_fields
theorem row303_source : sourceKey 303 ∈ geometry.profile (sourceOwner 303) := by decide +kernel
theorem row303_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 265 key0).FastValid geometry rowPose303 := by decide +kernel
theorem row303_illegal : ¬ geometry.LegalContact rowPose303 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row303_reject_checked)
theorem row303_classified : RowClassified 303 := by
  intro p generated legal
  have he : rowPose303 = p := Option.some.inj (row303_generated.symm.trans generated)
  subst p
  exact (row303_illegal legal).elim

def rowPose304 : Pose 7 := ⟨perm0, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row304_fields : pairFieldsMatchB 188160 facet0 facet266 key0 key304 rowPose304 = true := by decide +kernel
theorem row304_generated : rootPair 304 = some rowPose304 :=
  pairFieldsMatchB_sound (by decide) row304_fields
theorem row304_source : sourceKey 304 ∈ geometry.profile (sourceOwner 304) := by decide +kernel
theorem row304_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 266 key1).FastValid geometry rowPose304 := by decide +kernel
theorem row304_illegal : ¬ geometry.LegalContact rowPose304 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row304_reject_checked)
theorem row304_classified : RowClassified 304 := by
  intro p generated legal
  have he : rowPose304 = p := Option.some.inj (row304_generated.symm.trans generated)
  subst p
  exact (row304_illegal legal).elim

def rowPose305 : Pose 7 := ⟨perm21, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row305_fields : pairFieldsMatchB 188160 facet0 facet267 key0 key305 rowPose305 = true := by decide +kernel
theorem row305_generated : rootPair 305 = some rowPose305 :=
  pairFieldsMatchB_sound (by decide) row305_fields
theorem row305_source : sourceKey 305 ∈ geometry.profile (sourceOwner 305) := by decide +kernel
theorem row305_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 267 key0).FastValid geometry rowPose305 := by decide +kernel
theorem row305_illegal : ¬ geometry.LegalContact rowPose305 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row305_reject_checked)
theorem row305_classified : RowClassified 305 := by
  intro p generated legal
  have he : rowPose305 = p := Option.some.inj (row305_generated.symm.trans generated)
  subst p
  exact (row305_illegal legal).elim

def rowPose306 : Pose 7 := ⟨perm24, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row306_fields : pairFieldsMatchB 188160 facet0 facet267 key0 key306 rowPose306 = true := by decide +kernel
theorem row306_generated : rootPair 306 = some rowPose306 :=
  pairFieldsMatchB_sound (by decide) row306_fields
theorem row306_source : sourceKey 306 ∈ geometry.profile (sourceOwner 306) := by decide +kernel
theorem row306_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 717 key8).FastValid geometry rowPose306 := by decide +kernel
theorem row306_illegal : ¬ geometry.LegalContact rowPose306 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row306_reject_checked)
theorem row306_classified : RowClassified 306 := by
  intro p generated legal
  have he : rowPose306 = p := Option.some.inj (row306_generated.symm.trans generated)
  subst p
  exact (row306_illegal legal).elim

def rowPose307 : Pose 7 := ⟨perm37, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row307_fields : pairFieldsMatchB 188160 facet0 facet268 key0 key307 rowPose307 = true := by decide +kernel
theorem row307_generated : rootPair 307 = some rowPose307 :=
  pairFieldsMatchB_sound (by decide) row307_fields
theorem row307_source : sourceKey 307 ∈ geometry.profile (sourceOwner 307) := by decide +kernel
theorem row307_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 268 key0).FastValid geometry rowPose307 := by decide +kernel
theorem row307_illegal : ¬ geometry.LegalContact rowPose307 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row307_reject_checked)
theorem row307_classified : RowClassified 307 := by
  intro p generated legal
  have he : rowPose307 = p := Option.some.inj (row307_generated.symm.trans generated)
  subst p
  exact (row307_illegal legal).elim

def rowPose308 : Pose 7 := ⟨perm58, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row308_fields : pairFieldsMatchB 188160 facet0 facet269 key0 key308 rowPose308 = true := by decide +kernel
theorem row308_generated : rootPair 308 = some rowPose308 :=
  pairFieldsMatchB_sound (by decide) row308_fields
theorem row308_source : sourceKey 308 ∈ geometry.profile (sourceOwner 308) := by decide +kernel
theorem row308_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 269 key0).FastValid geometry rowPose308 := by decide +kernel
theorem row308_illegal : ¬ geometry.LegalContact rowPose308 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row308_reject_checked)
theorem row308_classified : RowClassified 308 := by
  intro p generated legal
  have he : rowPose308 = p := Option.some.inj (row308_generated.symm.trans generated)
  subst p
  exact (row308_illegal legal).elim

def rowPose309 : Pose 7 := ⟨perm71, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row309_fields : pairFieldsMatchB 188160 facet0 facet270 key0 key309 rowPose309 = true := by decide +kernel
theorem row309_generated : rootPair 309 = some rowPose309 :=
  pairFieldsMatchB_sound (by decide) row309_fields
theorem row309_source : sourceKey 309 ∈ geometry.profile (sourceOwner 309) := by decide +kernel
theorem row309_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 270 key1).FastValid geometry rowPose309 := by decide +kernel
theorem row309_illegal : ¬ geometry.LegalContact rowPose309 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row309_reject_checked)
theorem row309_classified : RowClassified 309 := by
  intro p generated legal
  have he : rowPose309 = p := Option.some.inj (row309_generated.symm.trans generated)
  subst p
  exact (row309_illegal legal).elim

def rowPose310 : Pose 7 := ⟨perm95, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row310_fields : pairFieldsMatchB 188160 facet0 facet271 key0 key310 rowPose310 = true := by decide +kernel
theorem row310_generated : rootPair 310 = some rowPose310 :=
  pairFieldsMatchB_sound (by decide) row310_fields
theorem row310_source : sourceKey 310 ∈ geometry.profile (sourceOwner 310) := by decide +kernel
theorem row310_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 271 key0).FastValid geometry rowPose310 := by decide +kernel
theorem row310_illegal : ¬ geometry.LegalContact rowPose310 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row310_reject_checked)
theorem row310_classified : RowClassified 310 := by
  intro p generated legal
  have he : rowPose310 = p := Option.some.inj (row310_generated.symm.trans generated)
  subst p
  exact (row310_illegal legal).elim

def rowPose311 : Pose 7 := ⟨perm111, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row311_fields : pairFieldsMatchB 188160 facet0 facet272 key0 key311 rowPose311 = true := by decide +kernel
theorem row311_generated : rootPair 311 = some rowPose311 :=
  pairFieldsMatchB_sound (by decide) row311_fields
theorem row311_source : sourceKey 311 ∈ geometry.profile (sourceOwner 311) := by decide +kernel
theorem row311_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 272 key1).FastValid geometry rowPose311 := by decide +kernel
theorem row311_illegal : ¬ geometry.LegalContact rowPose311 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row311_reject_checked)
theorem row311_classified : RowClassified 311 := by
  intro p generated legal
  have he : rowPose311 = p := Option.some.inj (row311_generated.symm.trans generated)
  subst p
  exact (row311_illegal legal).elim

def rowPose312 : Pose 7 := ⟨perm10, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row312_fields : pairFieldsMatchB 188160 facet0 facet273 key0 key312 rowPose312 = true := by decide +kernel
theorem row312_generated : rootPair 312 = some rowPose312 :=
  pairFieldsMatchB_sound (by decide) row312_fields
theorem row312_source : sourceKey 312 ∈ geometry.profile (sourceOwner 312) := by decide +kernel
theorem row312_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 273 key0).FastValid geometry rowPose312 := by decide +kernel
theorem row312_illegal : ¬ geometry.LegalContact rowPose312 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row312_reject_checked)
theorem row312_classified : RowClassified 312 := by
  intro p generated legal
  have he : rowPose312 = p := Option.some.inj (row312_generated.symm.trans generated)
  subst p
  exact (row312_illegal legal).elim

def rowPose313 : Pose 7 := ⟨perm22, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row313_fields : pairFieldsMatchB 188160 facet0 facet274 key0 key313 rowPose313 = true := by decide +kernel
theorem row313_generated : rootPair 313 = some rowPose313 :=
  pairFieldsMatchB_sound (by decide) row313_fields
theorem row313_source : sourceKey 313 ∈ geometry.profile (sourceOwner 313) := by decide +kernel
theorem row313_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 274 key1).FastValid geometry rowPose313 := by decide +kernel
theorem row313_illegal : ¬ geometry.LegalContact rowPose313 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row313_reject_checked)
theorem row313_classified : RowClassified 313 := by
  intro p generated legal
  have he : rowPose313 = p := Option.some.inj (row313_generated.symm.trans generated)
  subst p
  exact (row313_illegal legal).elim

def rowPose314 : Pose 7 := ⟨perm37, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row314_fields : pairFieldsMatchB 188160 facet0 facet275 key0 key314 rowPose314 = true := by decide +kernel
theorem row314_generated : rootPair 314 = some rowPose314 :=
  pairFieldsMatchB_sound (by decide) row314_fields
theorem row314_source : sourceKey 314 ∈ geometry.profile (sourceOwner 314) := by decide +kernel
theorem row314_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 275 key0).FastValid geometry rowPose314 := by decide +kernel
theorem row314_illegal : ¬ geometry.LegalContact rowPose314 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row314_reject_checked)
theorem row314_classified : RowClassified 314 := by
  intro p generated legal
  have he : rowPose314 = p := Option.some.inj (row314_generated.symm.trans generated)
  subst p
  exact (row314_illegal legal).elim

def rowPose315 : Pose 7 := ⟨perm58, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row315_fields : pairFieldsMatchB 188160 facet0 facet276 key0 key315 rowPose315 = true := by decide +kernel
theorem row315_generated : rootPair 315 = some rowPose315 :=
  pairFieldsMatchB_sound (by decide) row315_fields
theorem row315_source : sourceKey 315 ∈ geometry.profile (sourceOwner 315) := by decide +kernel
theorem row315_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 276 key0).FastValid geometry rowPose315 := by decide +kernel
theorem row315_illegal : ¬ geometry.LegalContact rowPose315 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row315_reject_checked)
theorem row315_classified : RowClassified 315 := by
  intro p generated legal
  have he : rowPose315 = p := Option.some.inj (row315_generated.symm.trans generated)
  subst p
  exact (row315_illegal legal).elim

def rowPose316 : Pose 7 := ⟨perm74, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row316_fields : pairFieldsMatchB 188160 facet0 facet277 key0 key316 rowPose316 = true := by decide +kernel
theorem row316_generated : rootPair 316 = some rowPose316 :=
  pairFieldsMatchB_sound (by decide) row316_fields
theorem row316_source : sourceKey 316 ∈ geometry.profile (sourceOwner 316) := by decide +kernel
theorem row316_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 277 key0).FastValid geometry rowPose316 := by decide +kernel
theorem row316_illegal : ¬ geometry.LegalContact rowPose316 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row316_reject_checked)
theorem row316_classified : RowClassified 316 := by
  intro p generated legal
  have he : rowPose316 = p := Option.some.inj (row316_generated.symm.trans generated)
  subst p
  exact (row316_illegal legal).elim

def rowPose317 : Pose 7 := ⟨perm69, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row317_fields : pairFieldsMatchB 188160 facet0 facet277 key0 key317 rowPose317 = true := by decide +kernel
theorem row317_generated : rootPair 317 = some rowPose317 :=
  pairFieldsMatchB_sound (by decide) row317_fields
theorem row317_source : sourceKey 317 ∈ geometry.profile (sourceOwner 317) := by decide +kernel
theorem row317_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 263 key8).FastValid geometry rowPose317 := by decide +kernel
theorem row317_illegal : ¬ geometry.LegalContact rowPose317 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row317_reject_checked)
theorem row317_classified : RowClassified 317 := by
  intro p generated legal
  have he : rowPose317 = p := Option.some.inj (row317_generated.symm.trans generated)
  subst p
  exact (row317_illegal legal).elim

def rowPose318 : Pose 7 := ⟨perm87, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row318_fields : pairFieldsMatchB 188160 facet0 facet278 key0 key318 rowPose318 = true := by decide +kernel
theorem row318_generated : rootPair 318 = some rowPose318 :=
  pairFieldsMatchB_sound (by decide) row318_fields
theorem row318_source : sourceKey 318 ∈ geometry.profile (sourceOwner 318) := by decide +kernel
theorem row318_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 278 key1).FastValid geometry rowPose318 := by decide +kernel
theorem row318_illegal : ¬ geometry.LegalContact rowPose318 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row318_reject_checked)
theorem row318_classified : RowClassified 318 := by
  intro p generated legal
  have he : rowPose318 = p := Option.some.inj (row318_generated.symm.trans generated)
  subst p
  exact (row318_illegal legal).elim

def rowPose319 : Pose 7 := ⟨perm96, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row319_fields : pairFieldsMatchB 188160 facet0 facet279 key0 key319 rowPose319 = true := by decide +kernel
theorem row319_generated : rootPair 319 = some rowPose319 :=
  pairFieldsMatchB_sound (by decide) row319_fields
theorem row319_source : sourceKey 319 ∈ geometry.profile (sourceOwner 319) := by decide +kernel
theorem row319_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 279 key1).FastValid geometry rowPose319 := by decide +kernel
theorem row319_illegal : ¬ geometry.LegalContact rowPose319 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row319_reject_checked)
theorem row319_classified : RowClassified 319 := by
  intro p generated legal
  have he : rowPose319 = p := Option.some.inj (row319_generated.symm.trans generated)
  subst p
  exact (row319_illegal legal).elim

theorem chunk09_classified (i : Fin 32) : RowClassified ⟨288 + i.val, by omega⟩ := by
  fin_cases i
  · exact row288_classified
  · exact row289_classified
  · exact row290_classified
  · exact row291_classified
  · exact row292_classified
  · exact row293_classified
  · exact row294_classified
  · exact row295_classified
  · exact row296_classified
  · exact row297_classified
  · exact row298_classified
  · exact row299_classified
  · exact row300_classified
  · exact row301_classified
  · exact row302_classified
  · exact row303_classified
  · exact row304_classified
  · exact row305_classified
  · exact row306_classified
  · exact row307_classified
  · exact row308_classified
  · exact row309_classified
  · exact row310_classified
  · exact row311_classified
  · exact row312_classified
  · exact row313_classified
  · exact row314_classified
  · exact row315_classified
  · exact row316_classified
  · exact row317_classified
  · exact row318_classified
  · exact row319_classified

theorem chunk09_source (i : Fin 32) : sourceKey ⟨288 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨288 + i.val, by omega⟩) := by
  fin_cases i
  · exact row288_source
  · exact row289_source
  · exact row290_source
  · exact row291_source
  · exact row292_source
  · exact row293_source
  · exact row294_source
  · exact row295_source
  · exact row296_source
  · exact row297_source
  · exact row298_source
  · exact row299_source
  · exact row300_source
  · exact row301_source
  · exact row302_source
  · exact row303_source
  · exact row304_source
  · exact row305_source
  · exact row306_source
  · exact row307_source
  · exact row308_source
  · exact row309_source
  · exact row310_source
  · exact row311_source
  · exact row312_source
  · exact row313_source
  · exact row314_source
  · exact row315_source
  · exact row316_source
  · exact row317_source
  · exact row318_source
  · exact row319_source

#print axioms chunk09_classified
end SparseMonotiles.Contact.RootZeroPilot7
