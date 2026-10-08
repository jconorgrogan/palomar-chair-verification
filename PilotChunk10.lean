module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose320 : Pose 7 := ⟨perm15, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row320_fields : pairFieldsMatchB 188160 facet0 facet280 key0 key320 rowPose320 = true := by decide +kernel
theorem row320_generated : rootPair 320 = some rowPose320 :=
  pairFieldsMatchB_sound (by decide) row320_fields
theorem row320_source : sourceKey 320 ∈ geometry.profile (sourceOwner 320) := by decide +kernel
theorem row320_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 280 key0).FastValid geometry rowPose320 := by decide +kernel
theorem row320_illegal : ¬ geometry.LegalContact rowPose320 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row320_reject_checked)
theorem row320_classified : RowClassified 320 := by
  intro p generated legal
  have he : rowPose320 = p := Option.some.inj (row320_generated.symm.trans generated)
  subst p
  exact (row320_illegal legal).elim

def rowPose321 : Pose 7 := ⟨perm24, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row321_fields : pairFieldsMatchB 188160 facet0 facet281 key0 key321 rowPose321 = true := by decide +kernel
theorem row321_generated : rootPair 321 = some rowPose321 :=
  pairFieldsMatchB_sound (by decide) row321_fields
theorem row321_source : sourceKey 321 ∈ geometry.profile (sourceOwner 321) := by decide +kernel
theorem row321_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 281 key0).FastValid geometry rowPose321 := by decide +kernel
theorem row321_illegal : ¬ geometry.LegalContact rowPose321 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row321_reject_checked)
theorem row321_classified : RowClassified 321 := by
  intro p generated legal
  have he : rowPose321 = p := Option.some.inj (row321_generated.symm.trans generated)
  subst p
  exact (row321_illegal legal).elim

def rowPose322 : Pose 7 := ⟨perm37, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row322_fields : pairFieldsMatchB 188160 facet0 facet282 key0 key322 rowPose322 = true := by decide +kernel
theorem row322_generated : rootPair 322 = some rowPose322 :=
  pairFieldsMatchB_sound (by decide) row322_fields
theorem row322_source : sourceKey 322 ∈ geometry.profile (sourceOwner 322) := by decide +kernel
theorem row322_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 226 key8).FastValid geometry rowPose322 := by decide +kernel
theorem row322_illegal : ¬ geometry.LegalContact rowPose322 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row322_reject_checked)
theorem row322_classified : RowClassified 322 := by
  intro p generated legal
  have he : rowPose322 = p := Option.some.inj (row322_generated.symm.trans generated)
  subst p
  exact (row322_illegal legal).elim

def rowPose323 : Pose 7 := ⟨perm42, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row323_fields : pairFieldsMatchB 188160 facet0 facet282 key0 key323 rowPose323 = true := by decide +kernel
theorem row323_generated : rootPair 323 = some rowPose323 :=
  pairFieldsMatchB_sound (by decide) row323_fields
theorem row323_source : sourceKey 323 ∈ geometry.profile (sourceOwner 323) := by decide +kernel
theorem row323_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 282 key0).FastValid geometry rowPose323 := by decide +kernel
theorem row323_illegal : ¬ geometry.LegalContact rowPose323 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row323_reject_checked)
theorem row323_classified : RowClassified 323 := by
  intro p generated legal
  have he : rowPose323 = p := Option.some.inj (row323_generated.symm.trans generated)
  subst p
  exact (row323_illegal legal).elim

def rowPose324 : Pose 7 := ⟨perm53, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row324_fields : pairFieldsMatchB 188160 facet0 facet283 key0 key324 rowPose324 = true := by decide +kernel
theorem row324_generated : rootPair 324 = some rowPose324 :=
  pairFieldsMatchB_sound (by decide) row324_fields
theorem row324_source : sourceKey 324 ∈ geometry.profile (sourceOwner 324) := by decide +kernel
theorem row324_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 283 key1).FastValid geometry rowPose324 := by decide +kernel
theorem row324_illegal : ¬ geometry.LegalContact rowPose324 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row324_reject_checked)
theorem row324_classified : RowClassified 324 := by
  intro p generated legal
  have he : rowPose324 = p := Option.some.inj (row324_generated.symm.trans generated)
  subst p
  exact (row324_illegal legal).elim

def rowPose325 : Pose 7 := ⟨perm74, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row325_fields : pairFieldsMatchB 188160 facet0 facet284 key0 key325 rowPose325 = true := by decide +kernel
theorem row325_generated : rootPair 325 = some rowPose325 :=
  pairFieldsMatchB_sound (by decide) row325_fields
theorem row325_source : sourceKey 325 ∈ geometry.profile (sourceOwner 325) := by decide +kernel
theorem row325_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 284 key1).FastValid geometry rowPose325 := by decide +kernel
theorem row325_illegal : ¬ geometry.LegalContact rowPose325 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row325_reject_checked)
theorem row325_classified : RowClassified 325 := by
  intro p generated legal
  have he : rowPose325 = p := Option.some.inj (row325_generated.symm.trans generated)
  subst p
  exact (row325_illegal legal).elim

def rowPose326 : Pose 7 := ⟨perm89, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row326_fields : pairFieldsMatchB 188160 facet0 facet285 key0 key326 rowPose326 = true := by decide +kernel
theorem row326_generated : rootPair 326 = some rowPose326 :=
  pairFieldsMatchB_sound (by decide) row326_fields
theorem row326_source : sourceKey 326 ∈ geometry.profile (sourceOwner 326) := by decide +kernel
theorem row326_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 285 key0).FastValid geometry rowPose326 := by decide +kernel
theorem row326_illegal : ¬ geometry.LegalContact rowPose326 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row326_reject_checked)
theorem row326_classified : RowClassified 326 := by
  intro p generated legal
  have he : rowPose326 = p := Option.some.inj (row326_generated.symm.trans generated)
  subst p
  exact (row326_illegal legal).elim

def rowPose327 : Pose 7 := ⟨perm101, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row327_fields : pairFieldsMatchB 188160 facet0 facet286 key0 key327 rowPose327 = true := by decide +kernel
theorem row327_generated : rootPair 327 = some rowPose327 :=
  pairFieldsMatchB_sound (by decide) row327_fields
theorem row327_source : sourceKey 327 ∈ geometry.profile (sourceOwner 327) := by decide +kernel
theorem row327_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 286 key1).FastValid geometry rowPose327 := by decide +kernel
theorem row327_illegal : ¬ geometry.LegalContact rowPose327 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row327_reject_checked)
theorem row327_classified : RowClassified 327 := by
  intro p generated legal
  have he : rowPose327 = p := Option.some.inj (row327_generated.symm.trans generated)
  subst p
  exact (row327_illegal legal).elim

def rowPose328 : Pose 7 := ⟨perm0, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row328_fields : pairFieldsMatchB 188160 facet0 facet287 key0 key328 rowPose328 = true := by decide +kernel
theorem row328_generated : rootPair 328 = some rowPose328 :=
  pairFieldsMatchB_sound (by decide) row328_fields
theorem row328_source : sourceKey 328 ∈ geometry.profile (sourceOwner 328) := by decide +kernel
theorem row328_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 287 key1).FastValid geometry rowPose328 := by decide +kernel
theorem row328_illegal : ¬ geometry.LegalContact rowPose328 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row328_reject_checked)
theorem row328_classified : RowClassified 328 := by
  intro p generated legal
  have he : rowPose328 = p := Option.some.inj (row328_generated.symm.trans generated)
  subst p
  exact (row328_illegal legal).elim

def rowPose329 : Pose 7 := ⟨perm21, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row329_fields : pairFieldsMatchB 188160 facet0 facet288 key0 key329 rowPose329 = true := by decide +kernel
theorem row329_generated : rootPair 329 = some rowPose329 :=
  pairFieldsMatchB_sound (by decide) row329_fields
theorem row329_source : sourceKey 329 ∈ geometry.profile (sourceOwner 329) := by decide +kernel
theorem row329_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 288 key0).FastValid geometry rowPose329 := by decide +kernel
theorem row329_illegal : ¬ geometry.LegalContact rowPose329 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row329_reject_checked)
theorem row329_classified : RowClassified 329 := by
  intro p generated legal
  have he : rowPose329 = p := Option.some.inj (row329_generated.symm.trans generated)
  subst p
  exact (row329_illegal legal).elim

def rowPose330 : Pose 7 := ⟨perm24, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row330_fields : pairFieldsMatchB 188160 facet0 facet288 key0 key330 rowPose330 = true := by decide +kernel
theorem row330_generated : rootPair 330 = some rowPose330 :=
  pairFieldsMatchB_sound (by decide) row330_fields
theorem row330_source : sourceKey 330 ∈ geometry.profile (sourceOwner 330) := by decide +kernel
theorem row330_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 738 key8).FastValid geometry rowPose330 := by decide +kernel
theorem row330_illegal : ¬ geometry.LegalContact rowPose330 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row330_reject_checked)
theorem row330_classified : RowClassified 330 := by
  intro p generated legal
  have he : rowPose330 = p := Option.some.inj (row330_generated.symm.trans generated)
  subst p
  exact (row330_illegal legal).elim

def rowPose331 : Pose 7 := ⟨perm37, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row331_fields : pairFieldsMatchB 188160 facet0 facet289 key0 key331 rowPose331 = true := by decide +kernel
theorem row331_generated : rootPair 331 = some rowPose331 :=
  pairFieldsMatchB_sound (by decide) row331_fields
theorem row331_source : sourceKey 331 ∈ geometry.profile (sourceOwner 331) := by decide +kernel
theorem row331_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 289 key0).FastValid geometry rowPose331 := by decide +kernel
theorem row331_illegal : ¬ geometry.LegalContact rowPose331 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row331_reject_checked)
theorem row331_classified : RowClassified 331 := by
  intro p generated legal
  have he : rowPose331 = p := Option.some.inj (row331_generated.symm.trans generated)
  subst p
  exact (row331_illegal legal).elim

def rowPose332 : Pose 7 := ⟨perm58, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row332_fields : pairFieldsMatchB 188160 facet0 facet290 key0 key332 rowPose332 = true := by decide +kernel
theorem row332_generated : rootPair 332 = some rowPose332 :=
  pairFieldsMatchB_sound (by decide) row332_fields
theorem row332_source : sourceKey 332 ∈ geometry.profile (sourceOwner 332) := by decide +kernel
theorem row332_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 290 key0).FastValid geometry rowPose332 := by decide +kernel
theorem row332_illegal : ¬ geometry.LegalContact rowPose332 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row332_reject_checked)
theorem row332_classified : RowClassified 332 := by
  intro p generated legal
  have he : rowPose332 = p := Option.some.inj (row332_generated.symm.trans generated)
  subst p
  exact (row332_illegal legal).elim

def rowPose333 : Pose 7 := ⟨perm71, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row333_fields : pairFieldsMatchB 188160 facet0 facet291 key0 key333 rowPose333 = true := by decide +kernel
theorem row333_generated : rootPair 333 = some rowPose333 :=
  pairFieldsMatchB_sound (by decide) row333_fields
theorem row333_source : sourceKey 333 ∈ geometry.profile (sourceOwner 333) := by decide +kernel
theorem row333_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 291 key1).FastValid geometry rowPose333 := by decide +kernel
theorem row333_illegal : ¬ geometry.LegalContact rowPose333 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row333_reject_checked)
theorem row333_classified : RowClassified 333 := by
  intro p generated legal
  have he : rowPose333 = p := Option.some.inj (row333_generated.symm.trans generated)
  subst p
  exact (row333_illegal legal).elim

def rowPose334 : Pose 7 := ⟨perm95, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row334_fields : pairFieldsMatchB 188160 facet0 facet292 key0 key334 rowPose334 = true := by decide +kernel
theorem row334_generated : rootPair 334 = some rowPose334 :=
  pairFieldsMatchB_sound (by decide) row334_fields
theorem row334_source : sourceKey 334 ∈ geometry.profile (sourceOwner 334) := by decide +kernel
theorem row334_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 292 key0).FastValid geometry rowPose334 := by decide +kernel
theorem row334_illegal : ¬ geometry.LegalContact rowPose334 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row334_reject_checked)
theorem row334_classified : RowClassified 334 := by
  intro p generated legal
  have he : rowPose334 = p := Option.some.inj (row334_generated.symm.trans generated)
  subst p
  exact (row334_illegal legal).elim

def rowPose335 : Pose 7 := ⟨perm111, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row335_fields : pairFieldsMatchB 188160 facet0 facet293 key0 key335 rowPose335 = true := by decide +kernel
theorem row335_generated : rootPair 335 = some rowPose335 :=
  pairFieldsMatchB_sound (by decide) row335_fields
theorem row335_source : sourceKey 335 ∈ geometry.profile (sourceOwner 335) := by decide +kernel
theorem row335_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 293 key1).FastValid geometry rowPose335 := by decide +kernel
theorem row335_illegal : ¬ geometry.LegalContact rowPose335 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row335_reject_checked)
theorem row335_classified : RowClassified 335 := by
  intro p generated legal
  have he : rowPose335 = p := Option.some.inj (row335_generated.symm.trans generated)
  subst p
  exact (row335_illegal legal).elim

def rowPose336 : Pose 7 := ⟨perm5, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row336_fields : pairFieldsMatchB 188160 facet0 facet294 key0 key336 rowPose336 = true := by decide +kernel
theorem row336_generated : rootPair 336 = some rowPose336 :=
  pairFieldsMatchB_sound (by decide) row336_fields
theorem row336_source : sourceKey 336 ∈ geometry.profile (sourceOwner 336) := by decide +kernel
theorem row336_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 294 key0).FastValid geometry rowPose336 := by decide +kernel
theorem row336_illegal : ¬ geometry.LegalContact rowPose336 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row336_reject_checked)
theorem row336_classified : RowClassified 336 := by
  intro p generated legal
  have he : rowPose336 = p := Option.some.inj (row336_generated.symm.trans generated)
  subst p
  exact (row336_illegal legal).elim

def rowPose337 : Pose 7 := ⟨perm21, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row337_fields : pairFieldsMatchB 188160 facet0 facet295 key0 key337 rowPose337 = true := by decide +kernel
theorem row337_generated : rootPair 337 = some rowPose337 :=
  pairFieldsMatchB_sound (by decide) row337_fields
theorem row337_source : sourceKey 337 ∈ geometry.profile (sourceOwner 337) := by decide +kernel
theorem row337_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 295 key1).FastValid geometry rowPose337 := by decide +kernel
theorem row337_illegal : ¬ geometry.LegalContact rowPose337 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row337_reject_checked)
theorem row337_classified : RowClassified 337 := by
  intro p generated legal
  have he : rowPose337 = p := Option.some.inj (row337_generated.symm.trans generated)
  subst p
  exact (row337_illegal legal).elim

def rowPose338 : Pose 7 := ⟨perm42, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row338_fields : pairFieldsMatchB 188160 facet0 facet296 key0 key338 rowPose338 = true := by decide +kernel
theorem row338_generated : rootPair 338 = some rowPose338 :=
  pairFieldsMatchB_sound (by decide) row338_fields
theorem row338_source : sourceKey 338 ∈ geometry.profile (sourceOwner 338) := by decide +kernel
theorem row338_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 296 key1).FastValid geometry rowPose338 := by decide +kernel
theorem row338_illegal : ¬ geometry.LegalContact rowPose338 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row338_reject_checked)
theorem row338_classified : RowClassified 338 := by
  intro p generated legal
  have he : rowPose338 = p := Option.some.inj (row338_generated.symm.trans generated)
  subst p
  exact (row338_illegal legal).elim

def rowPose339 : Pose 7 := ⟨perm53, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row339_fields : pairFieldsMatchB 188160 facet0 facet297 key0 key339 rowPose339 = true := by decide +kernel
theorem row339_generated : rootPair 339 = some rowPose339 :=
  pairFieldsMatchB_sound (by decide) row339_fields
theorem row339_source : sourceKey 339 ∈ geometry.profile (sourceOwner 339) := by decide +kernel
theorem row339_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 297 key0).FastValid geometry rowPose339 := by decide +kernel
theorem row339_illegal : ¬ geometry.LegalContact rowPose339 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row339_reject_checked)
theorem row339_classified : RowClassified 339 := by
  intro p generated legal
  have he : rowPose339 = p := Option.some.inj (row339_generated.symm.trans generated)
  subst p
  exact (row339_illegal legal).elim

def rowPose340 : Pose 7 := ⟨perm58, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row340_fields : pairFieldsMatchB 188160 facet0 facet297 key0 key340 rowPose340 = true := by decide +kernel
theorem row340_generated : rootPair 340 = some rowPose340 :=
  pairFieldsMatchB_sound (by decide) row340_fields
theorem row340_source : sourceKey 340 ∈ geometry.profile (sourceOwner 340) := by decide +kernel
theorem row340_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 409 key8).FastValid geometry rowPose340 := by decide +kernel
theorem row340_illegal : ¬ geometry.LegalContact rowPose340 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row340_reject_checked)
theorem row340_classified : RowClassified 340 := by
  intro p generated legal
  have he : rowPose340 = p := Option.some.inj (row340_generated.symm.trans generated)
  subst p
  exact (row340_illegal legal).elim

def rowPose341 : Pose 7 := ⟨perm69, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row341_fields : pairFieldsMatchB 188160 facet0 facet298 key0 key341 rowPose341 = true := by decide +kernel
theorem row341_generated : rootPair 341 = some rowPose341 :=
  pairFieldsMatchB_sound (by decide) row341_fields
theorem row341_source : sourceKey 341 ∈ geometry.profile (sourceOwner 341) := by decide +kernel
theorem row341_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 298 key0).FastValid geometry rowPose341 := by decide +kernel
theorem row341_illegal : ¬ geometry.LegalContact rowPose341 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row341_reject_checked)
theorem row341_classified : RowClassified 341 := by
  intro p generated legal
  have he : rowPose341 = p := Option.some.inj (row341_generated.symm.trans generated)
  subst p
  exact (row341_illegal legal).elim

def rowPose342 : Pose 7 := ⟨perm90, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row342_fields : pairFieldsMatchB 188160 facet0 facet299 key0 key342 rowPose342 = true := by decide +kernel
theorem row342_generated : rootPair 342 = some rowPose342 :=
  pairFieldsMatchB_sound (by decide) row342_fields
theorem row342_source : sourceKey 342 ∈ geometry.profile (sourceOwner 342) := by decide +kernel
theorem row342_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 299 key0).FastValid geometry rowPose342 := by decide +kernel
theorem row342_illegal : ¬ geometry.LegalContact rowPose342 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row342_reject_checked)
theorem row342_classified : RowClassified 342 := by
  intro p generated legal
  have he : rowPose342 = p := Option.some.inj (row342_generated.symm.trans generated)
  subst p
  exact (row342_illegal legal).elim

def rowPose343 : Pose 7 := ⟨perm106, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row343_fields : pairFieldsMatchB 188160 facet0 facet300 key0 key343 rowPose343 = true := by decide +kernel
theorem row343_generated : rootPair 343 = some rowPose343 :=
  pairFieldsMatchB_sound (by decide) row343_fields
theorem row343_source : sourceKey 343 ∈ geometry.profile (sourceOwner 343) := by decide +kernel
theorem row343_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 300 key1).FastValid geometry rowPose343 := by decide +kernel
theorem row343_illegal : ¬ geometry.LegalContact rowPose343 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row343_reject_checked)
theorem row343_classified : RowClassified 343 := by
  intro p generated legal
  have he : rowPose343 = p := Option.some.inj (row343_generated.symm.trans generated)
  subst p
  exact (row343_illegal legal).elim

def rowPose344 : Pose 7 := ⟨perm15, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row344_fields : pairFieldsMatchB 188160 facet0 facet301 key0 key344 rowPose344 = true := by decide +kernel
theorem row344_generated : rootPair 344 = some rowPose344 :=
  pairFieldsMatchB_sound (by decide) row344_fields
theorem row344_source : sourceKey 344 ∈ geometry.profile (sourceOwner 344) := by decide +kernel
theorem row344_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 301 key0).FastValid geometry rowPose344 := by decide +kernel
theorem row344_illegal : ¬ geometry.LegalContact rowPose344 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row344_reject_checked)
theorem row344_classified : RowClassified 344 := by
  intro p generated legal
  have he : rowPose344 = p := Option.some.inj (row344_generated.symm.trans generated)
  subst p
  exact (row344_illegal legal).elim

def rowPose345 : Pose 7 := ⟨perm24, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row345_fields : pairFieldsMatchB 188160 facet0 facet302 key0 key345 rowPose345 = true := by decide +kernel
theorem row345_generated : rootPair 345 = some rowPose345 :=
  pairFieldsMatchB_sound (by decide) row345_fields
theorem row345_source : sourceKey 345 ∈ geometry.profile (sourceOwner 345) := by decide +kernel
theorem row345_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 302 key0).FastValid geometry rowPose345 := by decide +kernel
theorem row345_illegal : ¬ geometry.LegalContact rowPose345 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row345_reject_checked)
theorem row345_classified : RowClassified 345 := by
  intro p generated legal
  have he : rowPose345 = p := Option.some.inj (row345_generated.symm.trans generated)
  subst p
  exact (row345_illegal legal).elim

def rowPose346 : Pose 7 := ⟨perm37, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row346_fields : pairFieldsMatchB 188160 facet0 facet303 key0 key346 rowPose346 = true := by decide +kernel
theorem row346_generated : rootPair 346 = some rowPose346 :=
  pairFieldsMatchB_sound (by decide) row346_fields
theorem row346_source : sourceKey 346 ∈ geometry.profile (sourceOwner 346) := by decide +kernel
theorem row346_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 247 key8).FastValid geometry rowPose346 := by decide +kernel
theorem row346_illegal : ¬ geometry.LegalContact rowPose346 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row346_reject_checked)
theorem row346_classified : RowClassified 346 := by
  intro p generated legal
  have he : rowPose346 = p := Option.some.inj (row346_generated.symm.trans generated)
  subst p
  exact (row346_illegal legal).elim

def rowPose347 : Pose 7 := ⟨perm42, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row347_fields : pairFieldsMatchB 188160 facet0 facet303 key0 key347 rowPose347 = true := by decide +kernel
theorem row347_generated : rootPair 347 = some rowPose347 :=
  pairFieldsMatchB_sound (by decide) row347_fields
theorem row347_source : sourceKey 347 ∈ geometry.profile (sourceOwner 347) := by decide +kernel
theorem row347_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 303 key0).FastValid geometry rowPose347 := by decide +kernel
theorem row347_illegal : ¬ geometry.LegalContact rowPose347 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row347_reject_checked)
theorem row347_classified : RowClassified 347 := by
  intro p generated legal
  have he : rowPose347 = p := Option.some.inj (row347_generated.symm.trans generated)
  subst p
  exact (row347_illegal legal).elim

def rowPose348 : Pose 7 := ⟨perm53, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row348_fields : pairFieldsMatchB 188160 facet0 facet304 key0 key348 rowPose348 = true := by decide +kernel
theorem row348_generated : rootPair 348 = some rowPose348 :=
  pairFieldsMatchB_sound (by decide) row348_fields
theorem row348_source : sourceKey 348 ∈ geometry.profile (sourceOwner 348) := by decide +kernel
theorem row348_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 304 key1).FastValid geometry rowPose348 := by decide +kernel
theorem row348_illegal : ¬ geometry.LegalContact rowPose348 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row348_reject_checked)
theorem row348_classified : RowClassified 348 := by
  intro p generated legal
  have he : rowPose348 = p := Option.some.inj (row348_generated.symm.trans generated)
  subst p
  exact (row348_illegal legal).elim

def rowPose349 : Pose 7 := ⟨perm74, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row349_fields : pairFieldsMatchB 188160 facet0 facet305 key0 key349 rowPose349 = true := by decide +kernel
theorem row349_generated : rootPair 349 = some rowPose349 :=
  pairFieldsMatchB_sound (by decide) row349_fields
theorem row349_source : sourceKey 349 ∈ geometry.profile (sourceOwner 349) := by decide +kernel
theorem row349_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 305 key1).FastValid geometry rowPose349 := by decide +kernel
theorem row349_illegal : ¬ geometry.LegalContact rowPose349 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row349_reject_checked)
theorem row349_classified : RowClassified 349 := by
  intro p generated legal
  have he : rowPose349 = p := Option.some.inj (row349_generated.symm.trans generated)
  subst p
  exact (row349_illegal legal).elim

def rowPose350 : Pose 7 := ⟨perm89, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row350_fields : pairFieldsMatchB 188160 facet0 facet306 key0 key350 rowPose350 = true := by decide +kernel
theorem row350_generated : rootPair 350 = some rowPose350 :=
  pairFieldsMatchB_sound (by decide) row350_fields
theorem row350_source : sourceKey 350 ∈ geometry.profile (sourceOwner 350) := by decide +kernel
theorem row350_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 306 key0).FastValid geometry rowPose350 := by decide +kernel
theorem row350_illegal : ¬ geometry.LegalContact rowPose350 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row350_reject_checked)
theorem row350_classified : RowClassified 350 := by
  intro p generated legal
  have he : rowPose350 = p := Option.some.inj (row350_generated.symm.trans generated)
  subst p
  exact (row350_illegal legal).elim

def rowPose351 : Pose 7 := ⟨perm101, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row351_fields : pairFieldsMatchB 188160 facet0 facet307 key0 key351 rowPose351 = true := by decide +kernel
theorem row351_generated : rootPair 351 = some rowPose351 :=
  pairFieldsMatchB_sound (by decide) row351_fields
theorem row351_source : sourceKey 351 ∈ geometry.profile (sourceOwner 351) := by decide +kernel
theorem row351_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 307 key1).FastValid geometry rowPose351 := by decide +kernel
theorem row351_illegal : ¬ geometry.LegalContact rowPose351 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row351_reject_checked)
theorem row351_classified : RowClassified 351 := by
  intro p generated legal
  have he : rowPose351 = p := Option.some.inj (row351_generated.symm.trans generated)
  subst p
  exact (row351_illegal legal).elim

theorem chunk10_classified (i : Fin 32) : RowClassified ⟨320 + i.val, by omega⟩ := by
  fin_cases i
  · exact row320_classified
  · exact row321_classified
  · exact row322_classified
  · exact row323_classified
  · exact row324_classified
  · exact row325_classified
  · exact row326_classified
  · exact row327_classified
  · exact row328_classified
  · exact row329_classified
  · exact row330_classified
  · exact row331_classified
  · exact row332_classified
  · exact row333_classified
  · exact row334_classified
  · exact row335_classified
  · exact row336_classified
  · exact row337_classified
  · exact row338_classified
  · exact row339_classified
  · exact row340_classified
  · exact row341_classified
  · exact row342_classified
  · exact row343_classified
  · exact row344_classified
  · exact row345_classified
  · exact row346_classified
  · exact row347_classified
  · exact row348_classified
  · exact row349_classified
  · exact row350_classified
  · exact row351_classified

theorem chunk10_source (i : Fin 32) : sourceKey ⟨320 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨320 + i.val, by omega⟩) := by
  fin_cases i
  · exact row320_source
  · exact row321_source
  · exact row322_source
  · exact row323_source
  · exact row324_source
  · exact row325_source
  · exact row326_source
  · exact row327_source
  · exact row328_source
  · exact row329_source
  · exact row330_source
  · exact row331_source
  · exact row332_source
  · exact row333_source
  · exact row334_source
  · exact row335_source
  · exact row336_source
  · exact row337_source
  · exact row338_source
  · exact row339_source
  · exact row340_source
  · exact row341_source
  · exact row342_source
  · exact row343_source
  · exact row344_source
  · exact row345_source
  · exact row346_source
  · exact row347_source
  · exact row348_source
  · exact row349_source
  · exact row350_source
  · exact row351_source

#print axioms chunk10_classified
end SparseMonotiles.Contact.RootZeroPilot7
