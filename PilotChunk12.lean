module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose384 : Pose 7 := ⟨perm0, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row384_fields : pairFieldsMatchB 188160 facet0 facet336 key0 key384 rowPose384 = true := by decide +kernel
theorem row384_generated : rootPair 384 = some rowPose384 :=
  pairFieldsMatchB_sound (by decide) row384_fields
theorem row384_source : sourceKey 384 ∈ geometry.profile (sourceOwner 384) := by decide +kernel
theorem row384_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 336 key1).FastValid geometry rowPose384 := by decide +kernel
theorem row384_illegal : ¬ geometry.LegalContact rowPose384 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row384_reject_checked)
theorem row384_classified : RowClassified 384 := by
  intro p generated legal
  have he : rowPose384 = p := Option.some.inj (row384_generated.symm.trans generated)
  subst p
  exact (row384_illegal legal).elim

def rowPose385 : Pose 7 := ⟨perm16, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row385_fields : pairFieldsMatchB 188160 facet0 facet337 key0 key385 rowPose385 = true := by decide +kernel
theorem row385_generated : rootPair 385 = some rowPose385 :=
  pairFieldsMatchB_sound (by decide) row385_fields
theorem row385_source : sourceKey 385 ∈ geometry.profile (sourceOwner 385) := by decide +kernel
theorem row385_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 337 key0).FastValid geometry rowPose385 := by decide +kernel
theorem row385_illegal : ¬ geometry.LegalContact rowPose385 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row385_reject_checked)
theorem row385_classified : RowClassified 385 := by
  intro p generated legal
  have he : rowPose385 = p := Option.some.inj (row385_generated.symm.trans generated)
  subst p
  exact (row385_illegal legal).elim

def rowPose386 : Pose 7 := ⟨perm40, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row386_fields : pairFieldsMatchB 188160 facet0 facet338 key0 key386 rowPose386 = true := by decide +kernel
theorem row386_generated : rootPair 386 = some rowPose386 :=
  pairFieldsMatchB_sound (by decide) row386_fields
theorem row386_source : sourceKey 386 ∈ geometry.profile (sourceOwner 386) := by decide +kernel
theorem row386_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 338 key1).FastValid geometry rowPose386 := by decide +kernel
theorem row386_illegal : ¬ geometry.LegalContact rowPose386 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row386_reject_checked)
theorem row386_classified : RowClassified 386 := by
  intro p generated legal
  have he : rowPose386 = p := Option.some.inj (row386_generated.symm.trans generated)
  subst p
  exact (row386_illegal legal).elim

def rowPose387 : Pose 7 := ⟨perm53, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row387_fields : pairFieldsMatchB 188160 facet0 facet339 key0 key387 rowPose387 = true := by decide +kernel
theorem row387_generated : rootPair 387 = some rowPose387 :=
  pairFieldsMatchB_sound (by decide) row387_fields
theorem row387_source : sourceKey 387 ∈ geometry.profile (sourceOwner 387) := by decide +kernel
theorem row387_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 339 key0).FastValid geometry rowPose387 := by decide +kernel
theorem row387_illegal : ¬ geometry.LegalContact rowPose387 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row387_reject_checked)
theorem row387_classified : RowClassified 387 := by
  intro p generated legal
  have he : rowPose387 = p := Option.some.inj (row387_generated.symm.trans generated)
  subst p
  exact (row387_illegal legal).elim

def rowPose388 : Pose 7 := ⟨perm74, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row388_fields : pairFieldsMatchB 188160 facet0 facet340 key0 key388 rowPose388 = true := by decide +kernel
theorem row388_generated : rootPair 388 = some rowPose388 :=
  pairFieldsMatchB_sound (by decide) row388_fields
theorem row388_source : sourceKey 388 ∈ geometry.profile (sourceOwner 388) := by decide +kernel
theorem row388_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 340 key0).FastValid geometry rowPose388 := by decide +kernel
theorem row388_illegal : ¬ geometry.LegalContact rowPose388 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row388_reject_checked)
theorem row388_classified : RowClassified 388 := by
  intro p generated legal
  have he : rowPose388 = p := Option.some.inj (row388_generated.symm.trans generated)
  subst p
  exact (row388_illegal legal).elim

def rowPose389 : Pose 7 := ⟨perm90, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row389_fields : pairFieldsMatchB 188160 facet0 facet341 key0 key389 rowPose389 = true := by decide +kernel
theorem row389_generated : rootPair 389 = some rowPose389 :=
  pairFieldsMatchB_sound (by decide) row389_fields
theorem row389_source : sourceKey 389 ∈ geometry.profile (sourceOwner 389) := by decide +kernel
theorem row389_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 341 key0).FastValid geometry rowPose389 := by decide +kernel
theorem row389_illegal : ¬ geometry.LegalContact rowPose389 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row389_reject_checked)
theorem row389_classified : RowClassified 389 := by
  intro p generated legal
  have he : rowPose389 = p := Option.some.inj (row389_generated.symm.trans generated)
  subst p
  exact (row389_illegal legal).elim

def rowPose390 : Pose 7 := ⟨perm87, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row390_fields : pairFieldsMatchB 188160 facet0 facet341 key0 key390 rowPose390 = true := by decide +kernel
theorem row390_generated : rootPair 390 = some rowPose390 :=
  pairFieldsMatchB_sound (by decide) row390_fields
theorem row390_source : sourceKey 390 ∈ geometry.profile (sourceOwner 390) := by decide +kernel
theorem row390_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 348 key8).FastValid geometry rowPose390 := by decide +kernel
theorem row390_illegal : ¬ geometry.LegalContact rowPose390 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row390_reject_checked)
theorem row390_classified : RowClassified 390 := by
  intro p generated legal
  have he : rowPose390 = p := Option.some.inj (row390_generated.symm.trans generated)
  subst p
  exact (row390_illegal legal).elim

def rowPose391 : Pose 7 := ⟨perm111, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row391_fields : pairFieldsMatchB 188160 facet0 facet342 key0 key391 rowPose391 = true := by decide +kernel
theorem row391_generated : rootPair 391 = some rowPose391 :=
  pairFieldsMatchB_sound (by decide) row391_fields
theorem row391_source : sourceKey 391 ∈ geometry.profile (sourceOwner 391) := by decide +kernel
theorem row391_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 342 key1).FastValid geometry rowPose391 := by decide +kernel
theorem row391_illegal : ¬ geometry.LegalContact rowPose391 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row391_reject_checked)
theorem row391_classified : RowClassified 391 := by
  intro p generated legal
  have he : rowPose391 = p := Option.some.inj (row391_generated.symm.trans generated)
  subst p
  exact (row391_illegal legal).elim

def rowPose392 : Pose 7 := ⟨perm5, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row392_fields : pairFieldsMatchB 188160 facet0 facet343 key0 key392 rowPose392 = true := by decide +kernel
theorem row392_generated : rootPair 392 = some rowPose392 :=
  pairFieldsMatchB_sound (by decide) row392_fields
theorem row392_source : sourceKey 392 ∈ geometry.profile (sourceOwner 392) := by decide +kernel
theorem row392_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 343 key0).FastValid geometry rowPose392 := by decide +kernel
theorem row392_illegal : ¬ geometry.LegalContact rowPose392 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row392_reject_checked)
theorem row392_classified : RowClassified 392 := by
  intro p generated legal
  have he : rowPose392 = p := Option.some.inj (row392_generated.symm.trans generated)
  subst p
  exact (row392_illegal legal).elim

def rowPose393 : Pose 7 := ⟨perm21, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row393_fields : pairFieldsMatchB 188160 facet0 facet344 key0 key393 rowPose393 = true := by decide +kernel
theorem row393_generated : rootPair 393 = some rowPose393 :=
  pairFieldsMatchB_sound (by decide) row393_fields
theorem row393_source : sourceKey 393 ∈ geometry.profile (sourceOwner 393) := by decide +kernel
theorem row393_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 344 key1).FastValid geometry rowPose393 := by decide +kernel
theorem row393_illegal : ¬ geometry.LegalContact rowPose393 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row393_reject_checked)
theorem row393_classified : RowClassified 393 := by
  intro p generated legal
  have he : rowPose393 = p := Option.some.inj (row393_generated.symm.trans generated)
  subst p
  exact (row393_illegal legal).elim

def rowPose394 : Pose 7 := ⟨perm42, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row394_fields : pairFieldsMatchB 188160 facet0 facet345 key0 key394 rowPose394 = true := by decide +kernel
theorem row394_generated : rootPair 394 = some rowPose394 :=
  pairFieldsMatchB_sound (by decide) row394_fields
theorem row394_source : sourceKey 394 ∈ geometry.profile (sourceOwner 394) := by decide +kernel
theorem row394_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 345 key1).FastValid geometry rowPose394 := by decide +kernel
theorem row394_illegal : ¬ geometry.LegalContact rowPose394 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row394_reject_checked)
theorem row394_classified : RowClassified 394 := by
  intro p generated legal
  have he : rowPose394 = p := Option.some.inj (row394_generated.symm.trans generated)
  subst p
  exact (row394_illegal legal).elim

def rowPose395 : Pose 7 := ⟨perm53, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row395_fields : pairFieldsMatchB 188160 facet0 facet346 key0 key395 rowPose395 = true := by decide +kernel
theorem row395_generated : rootPair 395 = some rowPose395 :=
  pairFieldsMatchB_sound (by decide) row395_fields
theorem row395_source : sourceKey 395 ∈ geometry.profile (sourceOwner 395) := by decide +kernel
theorem row395_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 346 key0).FastValid geometry rowPose395 := by decide +kernel
theorem row395_illegal : ¬ geometry.LegalContact rowPose395 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row395_reject_checked)
theorem row395_classified : RowClassified 395 := by
  intro p generated legal
  have he : rowPose395 = p := Option.some.inj (row395_generated.symm.trans generated)
  subst p
  exact (row395_illegal legal).elim

def rowPose396 : Pose 7 := ⟨perm58, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row396_fields : pairFieldsMatchB 188160 facet0 facet346 key0 key396 rowPose396 = true := by decide +kernel
theorem row396_generated : rootPair 396 = some rowPose396 :=
  pairFieldsMatchB_sound (by decide) row396_fields
theorem row396_source : sourceKey 396 ∈ geometry.profile (sourceOwner 396) := by decide +kernel
theorem row396_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 234 key8).FastValid geometry rowPose396 := by decide +kernel
theorem row396_illegal : ¬ geometry.LegalContact rowPose396 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row396_reject_checked)
theorem row396_classified : RowClassified 396 := by
  intro p generated legal
  have he : rowPose396 = p := Option.some.inj (row396_generated.symm.trans generated)
  subst p
  exact (row396_illegal legal).elim

def rowPose397 : Pose 7 := ⟨perm69, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row397_fields : pairFieldsMatchB 188160 facet0 facet347 key0 key397 rowPose397 = true := by decide +kernel
theorem row397_generated : rootPair 397 = some rowPose397 :=
  pairFieldsMatchB_sound (by decide) row397_fields
theorem row397_source : sourceKey 397 ∈ geometry.profile (sourceOwner 397) := by decide +kernel
theorem row397_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 347 key0).FastValid geometry rowPose397 := by decide +kernel
theorem row397_illegal : ¬ geometry.LegalContact rowPose397 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row397_reject_checked)
theorem row397_classified : RowClassified 397 := by
  intro p generated legal
  have he : rowPose397 = p := Option.some.inj (row397_generated.symm.trans generated)
  subst p
  exact (row397_illegal legal).elim

def rowPose398 : Pose 7 := ⟨perm90, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row398_fields : pairFieldsMatchB 188160 facet0 facet348 key0 key398 rowPose398 = true := by decide +kernel
theorem row398_generated : rootPair 398 = some rowPose398 :=
  pairFieldsMatchB_sound (by decide) row398_fields
theorem row398_source : sourceKey 398 ∈ geometry.profile (sourceOwner 398) := by decide +kernel
theorem row398_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 348 key0).FastValid geometry rowPose398 := by decide +kernel
theorem row398_illegal : ¬ geometry.LegalContact rowPose398 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row398_reject_checked)
theorem row398_classified : RowClassified 398 := by
  intro p generated legal
  have he : rowPose398 = p := Option.some.inj (row398_generated.symm.trans generated)
  subst p
  exact (row398_illegal legal).elim

def rowPose399 : Pose 7 := ⟨perm106, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row399_fields : pairFieldsMatchB 188160 facet0 facet349 key0 key399 rowPose399 = true := by decide +kernel
theorem row399_generated : rootPair 399 = some rowPose399 :=
  pairFieldsMatchB_sound (by decide) row399_fields
theorem row399_source : sourceKey 399 ∈ geometry.profile (sourceOwner 399) := by decide +kernel
theorem row399_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 349 key1).FastValid geometry rowPose399 := by decide +kernel
theorem row399_illegal : ¬ geometry.LegalContact rowPose399 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row399_reject_checked)
theorem row399_classified : RowClassified 399 := by
  intro p generated legal
  have he : rowPose399 = p := Option.some.inj (row399_generated.symm.trans generated)
  subst p
  exact (row399_illegal legal).elim

def rowPose400 : Pose 7 := ⟨perm0, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row400_fields : pairFieldsMatchB 188160 facet0 facet350 key0 key400 rowPose400 = true := by decide +kernel
theorem row400_generated : rootPair 400 = some rowPose400 :=
  pairFieldsMatchB_sound (by decide) row400_fields
theorem row400_source : sourceKey 400 ∈ geometry.profile (sourceOwner 400) := by decide +kernel
theorem row400_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 350 key0).FastValid geometry rowPose400 := by decide +kernel
theorem row400_illegal : ¬ geometry.LegalContact rowPose400 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row400_reject_checked)
theorem row400_classified : RowClassified 400 := by
  intro p generated legal
  have he : rowPose400 = p := Option.some.inj (row400_generated.symm.trans generated)
  subst p
  exact (row400_illegal legal).elim

def rowPose401 : Pose 7 := ⟨perm16, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row401_fields : pairFieldsMatchB 188160 facet0 facet351 key0 key401 rowPose401 = true := by decide +kernel
theorem row401_generated : rootPair 401 = some rowPose401 :=
  pairFieldsMatchB_sound (by decide) row401_fields
theorem row401_source : sourceKey 401 ∈ geometry.profile (sourceOwner 401) := by decide +kernel
theorem row401_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 351 key1).FastValid geometry rowPose401 := by decide +kernel
theorem row401_illegal : ¬ geometry.LegalContact rowPose401 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row401_reject_checked)
theorem row401_classified : RowClassified 401 := by
  intro p generated legal
  have he : rowPose401 = p := Option.some.inj (row401_generated.symm.trans generated)
  subst p
  exact (row401_illegal legal).elim

def rowPose402 : Pose 7 := ⟨perm40, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row402_fields : pairFieldsMatchB 188160 facet0 facet352 key0 key402 rowPose402 = true := by decide +kernel
theorem row402_generated : rootPair 402 = some rowPose402 :=
  pairFieldsMatchB_sound (by decide) row402_fields
theorem row402_source : sourceKey 402 ∈ geometry.profile (sourceOwner 402) := by decide +kernel
theorem row402_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 352 key0).FastValid geometry rowPose402 := by decide +kernel
theorem row402_illegal : ¬ geometry.LegalContact rowPose402 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row402_reject_checked)
theorem row402_classified : RowClassified 402 := by
  intro p generated legal
  have he : rowPose402 = p := Option.some.inj (row402_generated.symm.trans generated)
  subst p
  exact (row402_illegal legal).elim

def rowPose403 : Pose 7 := ⟨perm53, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row403_fields : pairFieldsMatchB 188160 facet0 facet353 key0 key403 rowPose403 = true := by decide +kernel
theorem row403_generated : rootPair 403 = some rowPose403 :=
  pairFieldsMatchB_sound (by decide) row403_fields
theorem row403_source : sourceKey 403 ∈ geometry.profile (sourceOwner 403) := by decide +kernel
theorem row403_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 353 key1).FastValid geometry rowPose403 := by decide +kernel
theorem row403_illegal : ¬ geometry.LegalContact rowPose403 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row403_reject_checked)
theorem row403_classified : RowClassified 403 := by
  intro p generated legal
  have he : rowPose403 = p := Option.some.inj (row403_generated.symm.trans generated)
  subst p
  exact (row403_illegal legal).elim

def rowPose404 : Pose 7 := ⟨perm74, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row404_fields : pairFieldsMatchB 188160 facet0 facet354 key0 key404 rowPose404 = true := by decide +kernel
theorem row404_generated : rootPair 404 = some rowPose404 :=
  pairFieldsMatchB_sound (by decide) row404_fields
theorem row404_source : sourceKey 404 ∈ geometry.profile (sourceOwner 404) := by decide +kernel
theorem row404_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 354 key1).FastValid geometry rowPose404 := by decide +kernel
theorem row404_illegal : ¬ geometry.LegalContact rowPose404 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row404_reject_checked)
theorem row404_classified : RowClassified 404 := by
  intro p generated legal
  have he : rowPose404 = p := Option.some.inj (row404_generated.symm.trans generated)
  subst p
  exact (row404_illegal legal).elim

def rowPose405 : Pose 7 := ⟨perm90, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row405_fields : pairFieldsMatchB 188160 facet0 facet355 key0 key405 rowPose405 = true := by decide +kernel
theorem row405_generated : rootPair 405 = some rowPose405 :=
  pairFieldsMatchB_sound (by decide) row405_fields
theorem row405_source : sourceKey 405 ∈ geometry.profile (sourceOwner 405) := by decide +kernel
theorem row405_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 383 key8).FastValid geometry rowPose405 := by decide +kernel
theorem row405_illegal : ¬ geometry.LegalContact rowPose405 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row405_reject_checked)
theorem row405_classified : RowClassified 405 := by
  intro p generated legal
  have he : rowPose405 = p := Option.some.inj (row405_generated.symm.trans generated)
  subst p
  exact (row405_illegal legal).elim

def rowPose406 : Pose 7 := ⟨perm87, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row406_fields : pairFieldsMatchB 188160 facet0 facet355 key0 key406 rowPose406 = true := by decide +kernel
theorem row406_generated : rootPair 406 = some rowPose406 :=
  pairFieldsMatchB_sound (by decide) row406_fields
theorem row406_source : sourceKey 406 ∈ geometry.profile (sourceOwner 406) := by decide +kernel
theorem row406_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 355 key0).FastValid geometry rowPose406 := by decide +kernel
theorem row406_illegal : ¬ geometry.LegalContact rowPose406 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row406_reject_checked)
theorem row406_classified : RowClassified 406 := by
  intro p generated legal
  have he : rowPose406 = p := Option.some.inj (row406_generated.symm.trans generated)
  subst p
  exact (row406_illegal legal).elim

def rowPose407 : Pose 7 := ⟨perm111, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row407_fields : pairFieldsMatchB 188160 facet0 facet356 key0 key407 rowPose407 = true := by decide +kernel
theorem row407_generated : rootPair 407 = some rowPose407 :=
  pairFieldsMatchB_sound (by decide) row407_fields
theorem row407_source : sourceKey 407 ∈ geometry.profile (sourceOwner 407) := by decide +kernel
theorem row407_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 356 key0).FastValid geometry rowPose407 := by decide +kernel
theorem row407_illegal : ¬ geometry.LegalContact rowPose407 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row407_reject_checked)
theorem row407_classified : RowClassified 407 := by
  intro p generated legal
  have he : rowPose407 = p := Option.some.inj (row407_generated.symm.trans generated)
  subst p
  exact (row407_illegal legal).elim

def rowPose408 : Pose 7 := ⟨perm0, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row408_fields : pairFieldsMatchB 188160 facet0 facet357 key0 key408 rowPose408 = true := by decide +kernel
theorem row408_generated : rootPair 408 = some rowPose408 :=
  pairFieldsMatchB_sound (by decide) row408_fields
theorem row408_source : sourceKey 408 ∈ geometry.profile (sourceOwner 408) := by decide +kernel
theorem row408_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 357 key0).FastValid geometry rowPose408 := by decide +kernel
theorem row408_illegal : ¬ geometry.LegalContact rowPose408 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row408_reject_checked)
theorem row408_classified : RowClassified 408 := by
  intro p generated legal
  have he : rowPose408 = p := Option.some.inj (row408_generated.symm.trans generated)
  subst p
  exact (row408_illegal legal).elim

def rowPose409 : Pose 7 := ⟨perm15, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row409_fields : pairFieldsMatchB 188160 facet0 facet357 key0 key409 rowPose409 = true := by decide +kernel
theorem row409_generated : rootPair 409 = some rowPose409 :=
  pairFieldsMatchB_sound (by decide) row409_fields
theorem row409_source : sourceKey 409 ∈ geometry.profile (sourceOwner 409) := by decide +kernel
theorem row409_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 133 key8).FastValid geometry rowPose409 := by decide +kernel
theorem row409_illegal : ¬ geometry.LegalContact rowPose409 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row409_reject_checked)
theorem row409_classified : RowClassified 409 := by
  intro p generated legal
  have he : rowPose409 = p := Option.some.inj (row409_generated.symm.trans generated)
  subst p
  exact (row409_illegal legal).elim

def rowPose410 : Pose 7 := ⟨perm21, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row410_fields : pairFieldsMatchB 188160 facet0 facet358 key0 key410 rowPose410 = true := by decide +kernel
theorem row410_generated : rootPair 410 = some rowPose410 :=
  pairFieldsMatchB_sound (by decide) row410_fields
theorem row410_source : sourceKey 410 ∈ geometry.profile (sourceOwner 410) := by decide +kernel
theorem row410_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 358 key1).FastValid geometry rowPose410 := by decide +kernel
theorem row410_illegal : ¬ geometry.LegalContact rowPose410 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row410_reject_checked)
theorem row410_classified : RowClassified 410 := by
  intro p generated legal
  have he : rowPose410 = p := Option.some.inj (row410_generated.symm.trans generated)
  subst p
  exact (row410_illegal legal).elim

def rowPose411 : Pose 7 := ⟨perm42, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row411_fields : pairFieldsMatchB 188160 facet0 facet359 key0 key411 rowPose411 = true := by decide +kernel
theorem row411_generated : rootPair 411 = some rowPose411 :=
  pairFieldsMatchB_sound (by decide) row411_fields
theorem row411_source : sourceKey 411 ∈ geometry.profile (sourceOwner 411) := by decide +kernel
theorem row411_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 359 key1).FastValid geometry rowPose411 := by decide +kernel
theorem row411_illegal : ¬ geometry.LegalContact rowPose411 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row411_reject_checked)
theorem row411_classified : RowClassified 411 := by
  intro p generated legal
  have he : rowPose411 = p := Option.some.inj (row411_generated.symm.trans generated)
  subst p
  exact (row411_illegal legal).elim

def rowPose412 : Pose 7 := ⟨perm55, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row412_fields : pairFieldsMatchB 188160 facet0 facet360 key0 key412 rowPose412 = true := by decide +kernel
theorem row412_generated : rootPair 412 = some rowPose412 :=
  pairFieldsMatchB_sound (by decide) row412_fields
theorem row412_source : sourceKey 412 ∈ geometry.profile (sourceOwner 412) := by decide +kernel
theorem row412_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 360 key0).FastValid geometry rowPose412 := by decide +kernel
theorem row412_illegal : ¬ geometry.LegalContact rowPose412 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row412_reject_checked)
theorem row412_classified : RowClassified 412 := by
  intro p generated legal
  have he : rowPose412 = p := Option.some.inj (row412_generated.symm.trans generated)
  subst p
  exact (row412_illegal legal).elim

def rowPose413 : Pose 7 := ⟨perm73, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row413_fields : pairFieldsMatchB 188160 facet0 facet361 key0 key413 rowPose413 = true := by decide +kernel
theorem row413_generated : rootPair 413 = some rowPose413 :=
  pairFieldsMatchB_sound (by decide) row413_fields
theorem row413_source : sourceKey 413 ∈ geometry.profile (sourceOwner 413) := by decide +kernel
theorem row413_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 361 key1).FastValid geometry rowPose413 := by decide +kernel
theorem row413_illegal : ¬ geometry.LegalContact rowPose413 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row413_reject_checked)
theorem row413_classified : RowClassified 413 := by
  intro p generated legal
  have he : rowPose413 = p := Option.some.inj (row413_generated.symm.trans generated)
  subst p
  exact (row413_illegal legal).elim

def rowPose414 : Pose 7 := ⟨perm87, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row414_fields : pairFieldsMatchB 188160 facet0 facet362 key0 key414 rowPose414 = true := by decide +kernel
theorem row414_generated : rootPair 414 = some rowPose414 :=
  pairFieldsMatchB_sound (by decide) row414_fields
theorem row414_source : sourceKey 414 ∈ geometry.profile (sourceOwner 414) := by decide +kernel
theorem row414_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 362 key0).FastValid geometry rowPose414 := by decide +kernel
theorem row414_illegal : ¬ geometry.LegalContact rowPose414 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row414_reject_checked)
theorem row414_classified : RowClassified 414 := by
  intro p generated legal
  have he : rowPose414 = p := Option.some.inj (row414_generated.symm.trans generated)
  subst p
  exact (row414_illegal legal).elim

def rowPose415 : Pose 7 := ⟨perm96, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row415_fields : pairFieldsMatchB 188160 facet0 facet363 key0 key415 rowPose415 = true := by decide +kernel
theorem row415_generated : rootPair 415 = some rowPose415 :=
  pairFieldsMatchB_sound (by decide) row415_fields
theorem row415_source : sourceKey 415 ∈ geometry.profile (sourceOwner 415) := by decide +kernel
theorem row415_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 363 key0).FastValid geometry rowPose415 := by decide +kernel
theorem row415_illegal : ¬ geometry.LegalContact rowPose415 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row415_reject_checked)
theorem row415_classified : RowClassified 415 := by
  intro p generated legal
  have he : rowPose415 = p := Option.some.inj (row415_generated.symm.trans generated)
  subst p
  exact (row415_illegal legal).elim

theorem chunk12_classified (i : Fin 32) : RowClassified ⟨384 + i.val, by omega⟩ := by
  fin_cases i
  · exact row384_classified
  · exact row385_classified
  · exact row386_classified
  · exact row387_classified
  · exact row388_classified
  · exact row389_classified
  · exact row390_classified
  · exact row391_classified
  · exact row392_classified
  · exact row393_classified
  · exact row394_classified
  · exact row395_classified
  · exact row396_classified
  · exact row397_classified
  · exact row398_classified
  · exact row399_classified
  · exact row400_classified
  · exact row401_classified
  · exact row402_classified
  · exact row403_classified
  · exact row404_classified
  · exact row405_classified
  · exact row406_classified
  · exact row407_classified
  · exact row408_classified
  · exact row409_classified
  · exact row410_classified
  · exact row411_classified
  · exact row412_classified
  · exact row413_classified
  · exact row414_classified
  · exact row415_classified

theorem chunk12_source (i : Fin 32) : sourceKey ⟨384 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨384 + i.val, by omega⟩) := by
  fin_cases i
  · exact row384_source
  · exact row385_source
  · exact row386_source
  · exact row387_source
  · exact row388_source
  · exact row389_source
  · exact row390_source
  · exact row391_source
  · exact row392_source
  · exact row393_source
  · exact row394_source
  · exact row395_source
  · exact row396_source
  · exact row397_source
  · exact row398_source
  · exact row399_source
  · exact row400_source
  · exact row401_source
  · exact row402_source
  · exact row403_source
  · exact row404_source
  · exact row405_source
  · exact row406_source
  · exact row407_source
  · exact row408_source
  · exact row409_source
  · exact row410_source
  · exact row411_source
  · exact row412_source
  · exact row413_source
  · exact row414_source
  · exact row415_source

#print axioms chunk12_classified
end SparseMonotiles.Contact.RootZeroPilot7
