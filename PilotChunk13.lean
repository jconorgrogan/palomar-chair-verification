module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose416 : Pose 7 := ⟨perm0, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row416_fields : pairFieldsMatchB 188160 facet0 facet364 key0 key416 rowPose416 = true := by decide +kernel
theorem row416_generated : rootPair 416 = some rowPose416 :=
  pairFieldsMatchB_sound (by decide) row416_fields
theorem row416_source : sourceKey 416 ∈ geometry.profile (sourceOwner 416) := by decide +kernel
theorem row416_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 371 key8).FastValid geometry rowPose416 := by decide +kernel
theorem row416_illegal : ¬ geometry.LegalContact rowPose416 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row416_reject_checked)
theorem row416_classified : RowClassified 416 := by
  intro p generated legal
  have he : rowPose416 = p := Option.some.inj (row416_generated.symm.trans generated)
  subst p
  exact (row416_illegal legal).elim

def rowPose417 : Pose 7 := ⟨perm15, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row417_fields : pairFieldsMatchB 188160 facet0 facet364 key0 key417 rowPose417 = true := by decide +kernel
theorem row417_generated : rootPair 417 = some rowPose417 :=
  pairFieldsMatchB_sound (by decide) row417_fields
theorem row417_source : sourceKey 417 ∈ geometry.profile (sourceOwner 417) := by decide +kernel
theorem row417_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 364 key0).FastValid geometry rowPose417 := by decide +kernel
theorem row417_illegal : ¬ geometry.LegalContact rowPose417 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row417_reject_checked)
theorem row417_classified : RowClassified 417 := by
  intro p generated legal
  have he : rowPose417 = p := Option.some.inj (row417_generated.symm.trans generated)
  subst p
  exact (row417_illegal legal).elim

def rowPose418 : Pose 7 := ⟨perm21, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row418_fields : pairFieldsMatchB 188160 facet0 facet365 key0 key418 rowPose418 = true := by decide +kernel
theorem row418_generated : rootPair 418 = some rowPose418 :=
  pairFieldsMatchB_sound (by decide) row418_fields
theorem row418_source : sourceKey 418 ∈ geometry.profile (sourceOwner 418) := by decide +kernel
theorem row418_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 365 key0).FastValid geometry rowPose418 := by decide +kernel
theorem row418_illegal : ¬ geometry.LegalContact rowPose418 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row418_reject_checked)
theorem row418_classified : RowClassified 418 := by
  intro p generated legal
  have he : rowPose418 = p := Option.some.inj (row418_generated.symm.trans generated)
  subst p
  exact (row418_illegal legal).elim

def rowPose419 : Pose 7 := ⟨perm42, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row419_fields : pairFieldsMatchB 188160 facet0 facet366 key0 key419 rowPose419 = true := by decide +kernel
theorem row419_generated : rootPair 419 = some rowPose419 :=
  pairFieldsMatchB_sound (by decide) row419_fields
theorem row419_source : sourceKey 419 ∈ geometry.profile (sourceOwner 419) := by decide +kernel
theorem row419_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 366 key0).FastValid geometry rowPose419 := by decide +kernel
theorem row419_illegal : ¬ geometry.LegalContact rowPose419 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row419_reject_checked)
theorem row419_classified : RowClassified 419 := by
  intro p generated legal
  have he : rowPose419 = p := Option.some.inj (row419_generated.symm.trans generated)
  subst p
  exact (row419_illegal legal).elim

def rowPose420 : Pose 7 := ⟨perm55, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row420_fields : pairFieldsMatchB 188160 facet0 facet367 key0 key420 rowPose420 = true := by decide +kernel
theorem row420_generated : rootPair 420 = some rowPose420 :=
  pairFieldsMatchB_sound (by decide) row420_fields
theorem row420_source : sourceKey 420 ∈ geometry.profile (sourceOwner 420) := by decide +kernel
theorem row420_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 367 key1).FastValid geometry rowPose420 := by decide +kernel
theorem row420_illegal : ¬ geometry.LegalContact rowPose420 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row420_reject_checked)
theorem row420_classified : RowClassified 420 := by
  intro p generated legal
  have he : rowPose420 = p := Option.some.inj (row420_generated.symm.trans generated)
  subst p
  exact (row420_illegal legal).elim

def rowPose421 : Pose 7 := ⟨perm73, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row421_fields : pairFieldsMatchB 188160 facet0 facet368 key0 key421 rowPose421 = true := by decide +kernel
theorem row421_generated : rootPair 421 = some rowPose421 :=
  pairFieldsMatchB_sound (by decide) row421_fields
theorem row421_source : sourceKey 421 ∈ geometry.profile (sourceOwner 421) := by decide +kernel
theorem row421_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 368 key0).FastValid geometry rowPose421 := by decide +kernel
theorem row421_illegal : ¬ geometry.LegalContact rowPose421 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row421_reject_checked)
theorem row421_classified : RowClassified 421 := by
  intro p generated legal
  have he : rowPose421 = p := Option.some.inj (row421_generated.symm.trans generated)
  subst p
  exact (row421_illegal legal).elim

def rowPose422 : Pose 7 := ⟨perm87, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row422_fields : pairFieldsMatchB 188160 facet0 facet369 key0 key422 rowPose422 = true := by decide +kernel
theorem row422_generated : rootPair 422 = some rowPose422 :=
  pairFieldsMatchB_sound (by decide) row422_fields
theorem row422_source : sourceKey 422 ∈ geometry.profile (sourceOwner 422) := by decide +kernel
theorem row422_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 369 key1).FastValid geometry rowPose422 := by decide +kernel
theorem row422_illegal : ¬ geometry.LegalContact rowPose422 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row422_reject_checked)
theorem row422_classified : RowClassified 422 := by
  intro p generated legal
  have he : rowPose422 = p := Option.some.inj (row422_generated.symm.trans generated)
  subst p
  exact (row422_illegal legal).elim

def rowPose423 : Pose 7 := ⟨perm96, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row423_fields : pairFieldsMatchB 188160 facet0 facet370 key0 key423 rowPose423 = true := by decide +kernel
theorem row423_generated : rootPair 423 = some rowPose423 :=
  pairFieldsMatchB_sound (by decide) row423_fields
theorem row423_source : sourceKey 423 ∈ geometry.profile (sourceOwner 423) := by decide +kernel
theorem row423_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 370 key1).FastValid geometry rowPose423 := by decide +kernel
theorem row423_illegal : ¬ geometry.LegalContact rowPose423 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row423_reject_checked)
theorem row423_classified : RowClassified 423 := by
  intro p generated legal
  have he : rowPose423 = p := Option.some.inj (row423_generated.symm.trans generated)
  subst p
  exact (row423_illegal legal).elim

def rowPose424 : Pose 7 := ⟨perm0, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row424_fields : pairFieldsMatchB 188160 facet0 facet371 key0 key424 rowPose424 = true := by decide +kernel
theorem row424_generated : rootPair 424 = some rowPose424 :=
  pairFieldsMatchB_sound (by decide) row424_fields
theorem row424_source : sourceKey 424 ∈ geometry.profile (sourceOwner 424) := by decide +kernel
theorem row424_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 371 key1).FastValid geometry rowPose424 := by decide +kernel
theorem row424_illegal : ¬ geometry.LegalContact rowPose424 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row424_reject_checked)
theorem row424_classified : RowClassified 424 := by
  intro p generated legal
  have he : rowPose424 = p := Option.some.inj (row424_generated.symm.trans generated)
  subst p
  exact (row424_illegal legal).elim

def rowPose425 : Pose 7 := ⟨perm16, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row425_fields : pairFieldsMatchB 188160 facet0 facet372 key0 key425 rowPose425 = true := by decide +kernel
theorem row425_generated : rootPair 425 = some rowPose425 :=
  pairFieldsMatchB_sound (by decide) row425_fields
theorem row425_source : sourceKey 425 ∈ geometry.profile (sourceOwner 425) := by decide +kernel
theorem row425_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 372 key0).FastValid geometry rowPose425 := by decide +kernel
theorem row425_illegal : ¬ geometry.LegalContact rowPose425 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row425_reject_checked)
theorem row425_classified : RowClassified 425 := by
  intro p generated legal
  have he : rowPose425 = p := Option.some.inj (row425_generated.symm.trans generated)
  subst p
  exact (row425_illegal legal).elim

def rowPose426 : Pose 7 := ⟨perm40, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row426_fields : pairFieldsMatchB 188160 facet0 facet373 key0 key426 rowPose426 = true := by decide +kernel
theorem row426_generated : rootPair 426 = some rowPose426 :=
  pairFieldsMatchB_sound (by decide) row426_fields
theorem row426_source : sourceKey 426 ∈ geometry.profile (sourceOwner 426) := by decide +kernel
theorem row426_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 373 key1).FastValid geometry rowPose426 := by decide +kernel
theorem row426_illegal : ¬ geometry.LegalContact rowPose426 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row426_reject_checked)
theorem row426_classified : RowClassified 426 := by
  intro p generated legal
  have he : rowPose426 = p := Option.some.inj (row426_generated.symm.trans generated)
  subst p
  exact (row426_illegal legal).elim

def rowPose427 : Pose 7 := ⟨perm53, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row427_fields : pairFieldsMatchB 188160 facet0 facet374 key0 key427 rowPose427 = true := by decide +kernel
theorem row427_generated : rootPair 427 = some rowPose427 :=
  pairFieldsMatchB_sound (by decide) row427_fields
theorem row427_source : sourceKey 427 ∈ geometry.profile (sourceOwner 427) := by decide +kernel
theorem row427_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 374 key0).FastValid geometry rowPose427 := by decide +kernel
theorem row427_illegal : ¬ geometry.LegalContact rowPose427 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row427_reject_checked)
theorem row427_classified : RowClassified 427 := by
  intro p generated legal
  have he : rowPose427 = p := Option.some.inj (row427_generated.symm.trans generated)
  subst p
  exact (row427_illegal legal).elim

def rowPose428 : Pose 7 := ⟨perm74, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row428_fields : pairFieldsMatchB 188160 facet0 facet375 key0 key428 rowPose428 = true := by decide +kernel
theorem row428_generated : rootPair 428 = some rowPose428 :=
  pairFieldsMatchB_sound (by decide) row428_fields
theorem row428_source : sourceKey 428 ∈ geometry.profile (sourceOwner 428) := by decide +kernel
theorem row428_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 375 key0).FastValid geometry rowPose428 := by decide +kernel
theorem row428_illegal : ¬ geometry.LegalContact rowPose428 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row428_reject_checked)
theorem row428_classified : RowClassified 428 := by
  intro p generated legal
  have he : rowPose428 = p := Option.some.inj (row428_generated.symm.trans generated)
  subst p
  exact (row428_illegal legal).elim

def rowPose429 : Pose 7 := ⟨perm90, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row429_fields : pairFieldsMatchB 188160 facet0 facet376 key0 key429 rowPose429 = true := by decide +kernel
theorem row429_generated : rootPair 429 = some rowPose429 :=
  pairFieldsMatchB_sound (by decide) row429_fields
theorem row429_source : sourceKey 429 ∈ geometry.profile (sourceOwner 429) := by decide +kernel
theorem row429_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 376 key0).FastValid geometry rowPose429 := by decide +kernel
theorem row429_illegal : ¬ geometry.LegalContact rowPose429 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row429_reject_checked)
theorem row429_classified : RowClassified 429 := by
  intro p generated legal
  have he : rowPose429 = p := Option.some.inj (row429_generated.symm.trans generated)
  subst p
  exact (row429_illegal legal).elim

def rowPose430 : Pose 7 := ⟨perm87, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row430_fields : pairFieldsMatchB 188160 facet0 facet376 key0 key430 rowPose430 = true := by decide +kernel
theorem row430_generated : rootPair 430 = some rowPose430 :=
  pairFieldsMatchB_sound (by decide) row430_fields
theorem row430_source : sourceKey 430 ∈ geometry.profile (sourceOwner 430) := by decide +kernel
theorem row430_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 369 key8).FastValid geometry rowPose430 := by decide +kernel
theorem row430_illegal : ¬ geometry.LegalContact rowPose430 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row430_reject_checked)
theorem row430_classified : RowClassified 430 := by
  intro p generated legal
  have he : rowPose430 = p := Option.some.inj (row430_generated.symm.trans generated)
  subst p
  exact (row430_illegal legal).elim

def rowPose431 : Pose 7 := ⟨perm111, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row431_fields : pairFieldsMatchB 188160 facet0 facet377 key0 key431 rowPose431 = true := by decide +kernel
theorem row431_generated : rootPair 431 = some rowPose431 :=
  pairFieldsMatchB_sound (by decide) row431_fields
theorem row431_source : sourceKey 431 ∈ geometry.profile (sourceOwner 431) := by decide +kernel
theorem row431_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 377 key1).FastValid geometry rowPose431 := by decide +kernel
theorem row431_illegal : ¬ geometry.LegalContact rowPose431 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row431_reject_checked)
theorem row431_classified : RowClassified 431 := by
  intro p generated legal
  have he : rowPose431 = p := Option.some.inj (row431_generated.symm.trans generated)
  subst p
  exact (row431_illegal legal).elim

def rowPose432 : Pose 7 := ⟨perm5, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row432_fields : pairFieldsMatchB 188160 facet0 facet378 key0 key432 rowPose432 = true := by decide +kernel
theorem row432_generated : rootPair 432 = some rowPose432 :=
  pairFieldsMatchB_sound (by decide) row432_fields
theorem row432_source : sourceKey 432 ∈ geometry.profile (sourceOwner 432) := by decide +kernel
theorem row432_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 378 key1).FastValid geometry rowPose432 := by decide +kernel
theorem row432_illegal : ¬ geometry.LegalContact rowPose432 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row432_reject_checked)
theorem row432_classified : RowClassified 432 := by
  intro p generated legal
  have he : rowPose432 = p := Option.some.inj (row432_generated.symm.trans generated)
  subst p
  exact (row432_illegal legal).elim

def rowPose433 : Pose 7 := ⟨perm21, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row433_fields : pairFieldsMatchB 188160 facet0 facet379 key0 key433 rowPose433 = true := by decide +kernel
theorem row433_generated : rootPair 433 = some rowPose433 :=
  pairFieldsMatchB_sound (by decide) row433_fields
theorem row433_source : sourceKey 433 ∈ geometry.profile (sourceOwner 433) := by decide +kernel
theorem row433_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 379 key0).FastValid geometry rowPose433 := by decide +kernel
theorem row433_illegal : ¬ geometry.LegalContact rowPose433 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row433_reject_checked)
theorem row433_classified : RowClassified 433 := by
  intro p generated legal
  have he : rowPose433 = p := Option.some.inj (row433_generated.symm.trans generated)
  subst p
  exact (row433_illegal legal).elim

def rowPose434 : Pose 7 := ⟨perm42, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row434_fields : pairFieldsMatchB 188160 facet0 facet380 key0 key434 rowPose434 = true := by decide +kernel
theorem row434_generated : rootPair 434 = some rowPose434 :=
  pairFieldsMatchB_sound (by decide) row434_fields
theorem row434_source : sourceKey 434 ∈ geometry.profile (sourceOwner 434) := by decide +kernel
theorem row434_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 380 key0).FastValid geometry rowPose434 := by decide +kernel
theorem row434_illegal : ¬ geometry.LegalContact rowPose434 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row434_reject_checked)
theorem row434_classified : RowClassified 434 := by
  intro p generated legal
  have he : rowPose434 = p := Option.some.inj (row434_generated.symm.trans generated)
  subst p
  exact (row434_illegal legal).elim

def rowPose435 : Pose 7 := ⟨perm53, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row435_fields : pairFieldsMatchB 188160 facet0 facet381 key0 key435 rowPose435 = true := by decide +kernel
theorem row435_generated : rootPair 435 = some rowPose435 :=
  pairFieldsMatchB_sound (by decide) row435_fields
theorem row435_source : sourceKey 435 ∈ geometry.profile (sourceOwner 435) := by decide +kernel
theorem row435_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 353 key8).FastValid geometry rowPose435 := by decide +kernel
theorem row435_illegal : ¬ geometry.LegalContact rowPose435 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row435_reject_checked)
theorem row435_classified : RowClassified 435 := by
  intro p generated legal
  have he : rowPose435 = p := Option.some.inj (row435_generated.symm.trans generated)
  subst p
  exact (row435_illegal legal).elim

def rowPose436 : Pose 7 := ⟨perm58, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row436_fields : pairFieldsMatchB 188160 facet0 facet381 key0 key436 rowPose436 = true := by decide +kernel
theorem row436_generated : rootPair 436 = some rowPose436 :=
  pairFieldsMatchB_sound (by decide) row436_fields
theorem row436_source : sourceKey 436 ∈ geometry.profile (sourceOwner 436) := by decide +kernel
theorem row436_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 381 key0).FastValid geometry rowPose436 := by decide +kernel
theorem row436_illegal : ¬ geometry.LegalContact rowPose436 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row436_reject_checked)
theorem row436_classified : RowClassified 436 := by
  intro p generated legal
  have he : rowPose436 = p := Option.some.inj (row436_generated.symm.trans generated)
  subst p
  exact (row436_illegal legal).elim

def rowPose437 : Pose 7 := ⟨perm69, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row437_fields : pairFieldsMatchB 188160 facet0 facet382 key0 key437 rowPose437 = true := by decide +kernel
theorem row437_generated : rootPair 437 = some rowPose437 :=
  pairFieldsMatchB_sound (by decide) row437_fields
theorem row437_source : sourceKey 437 ∈ geometry.profile (sourceOwner 437) := by decide +kernel
theorem row437_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 382 key1).FastValid geometry rowPose437 := by decide +kernel
theorem row437_illegal : ¬ geometry.LegalContact rowPose437 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row437_reject_checked)
theorem row437_classified : RowClassified 437 := by
  intro p generated legal
  have he : rowPose437 = p := Option.some.inj (row437_generated.symm.trans generated)
  subst p
  exact (row437_illegal legal).elim

def rowPose438 : Pose 7 := ⟨perm90, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row438_fields : pairFieldsMatchB 188160 facet0 facet383 key0 key438 rowPose438 = true := by decide +kernel
theorem row438_generated : rootPair 438 = some rowPose438 :=
  pairFieldsMatchB_sound (by decide) row438_fields
theorem row438_source : sourceKey 438 ∈ geometry.profile (sourceOwner 438) := by decide +kernel
theorem row438_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 383 key1).FastValid geometry rowPose438 := by decide +kernel
theorem row438_illegal : ¬ geometry.LegalContact rowPose438 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row438_reject_checked)
theorem row438_classified : RowClassified 438 := by
  intro p generated legal
  have he : rowPose438 = p := Option.some.inj (row438_generated.symm.trans generated)
  subst p
  exact (row438_illegal legal).elim

def rowPose439 : Pose 7 := ⟨perm106, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row439_fields : pairFieldsMatchB 188160 facet0 facet384 key0 key439 rowPose439 = true := by decide +kernel
theorem row439_generated : rootPair 439 = some rowPose439 :=
  pairFieldsMatchB_sound (by decide) row439_fields
theorem row439_source : sourceKey 439 ∈ geometry.profile (sourceOwner 439) := by decide +kernel
theorem row439_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 384 key0).FastValid geometry rowPose439 := by decide +kernel
theorem row439_illegal : ¬ geometry.LegalContact rowPose439 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row439_reject_checked)
theorem row439_classified : RowClassified 439 := by
  intro p generated legal
  have he : rowPose439 = p := Option.some.inj (row439_generated.symm.trans generated)
  subst p
  exact (row439_illegal legal).elim

def rowPose440 : Pose 7 := ⟨perm0, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row440_fields : pairFieldsMatchB 188160 facet0 facet385 key0 key440 rowPose440 = true := by decide +kernel
theorem row440_generated : rootPair 440 = some rowPose440 :=
  pairFieldsMatchB_sound (by decide) row440_fields
theorem row440_source : sourceKey 440 ∈ geometry.profile (sourceOwner 440) := by decide +kernel
theorem row440_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 385 key0).FastValid geometry rowPose440 := by decide +kernel
theorem row440_illegal : ¬ geometry.LegalContact rowPose440 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row440_reject_checked)
theorem row440_classified : RowClassified 440 := by
  intro p generated legal
  have he : rowPose440 = p := Option.some.inj (row440_generated.symm.trans generated)
  subst p
  exact (row440_illegal legal).elim

def rowPose441 : Pose 7 := ⟨perm16, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row441_fields : pairFieldsMatchB 188160 facet0 facet386 key0 key441 rowPose441 = true := by decide +kernel
theorem row441_generated : rootPair 441 = some rowPose441 :=
  pairFieldsMatchB_sound (by decide) row441_fields
theorem row441_source : sourceKey 441 ∈ geometry.profile (sourceOwner 441) := by decide +kernel
theorem row441_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 386 key1).FastValid geometry rowPose441 := by decide +kernel
theorem row441_illegal : ¬ geometry.LegalContact rowPose441 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row441_reject_checked)
theorem row441_classified : RowClassified 441 := by
  intro p generated legal
  have he : rowPose441 = p := Option.some.inj (row441_generated.symm.trans generated)
  subst p
  exact (row441_illegal legal).elim

def rowPose442 : Pose 7 := ⟨perm40, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row442_fields : pairFieldsMatchB 188160 facet0 facet387 key0 key442 rowPose442 = true := by decide +kernel
theorem row442_generated : rootPair 442 = some rowPose442 :=
  pairFieldsMatchB_sound (by decide) row442_fields
theorem row442_source : sourceKey 442 ∈ geometry.profile (sourceOwner 442) := by decide +kernel
theorem row442_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 387 key0).FastValid geometry rowPose442 := by decide +kernel
theorem row442_illegal : ¬ geometry.LegalContact rowPose442 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row442_reject_checked)
theorem row442_classified : RowClassified 442 := by
  intro p generated legal
  have he : rowPose442 = p := Option.some.inj (row442_generated.symm.trans generated)
  subst p
  exact (row442_illegal legal).elim

def rowPose443 : Pose 7 := ⟨perm53, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row443_fields : pairFieldsMatchB 188160 facet0 facet388 key0 key443 rowPose443 = true := by decide +kernel
theorem row443_generated : rootPair 443 = some rowPose443 :=
  pairFieldsMatchB_sound (by decide) row443_fields
theorem row443_source : sourceKey 443 ∈ geometry.profile (sourceOwner 443) := by decide +kernel
theorem row443_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 388 key1).FastValid geometry rowPose443 := by decide +kernel
theorem row443_illegal : ¬ geometry.LegalContact rowPose443 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row443_reject_checked)
theorem row443_classified : RowClassified 443 := by
  intro p generated legal
  have he : rowPose443 = p := Option.some.inj (row443_generated.symm.trans generated)
  subst p
  exact (row443_illegal legal).elim

def rowPose444 : Pose 7 := ⟨perm74, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row444_fields : pairFieldsMatchB 188160 facet0 facet389 key0 key444 rowPose444 = true := by decide +kernel
theorem row444_generated : rootPair 444 = some rowPose444 :=
  pairFieldsMatchB_sound (by decide) row444_fields
theorem row444_source : sourceKey 444 ∈ geometry.profile (sourceOwner 444) := by decide +kernel
theorem row444_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 389 key1).FastValid geometry rowPose444 := by decide +kernel
theorem row444_illegal : ¬ geometry.LegalContact rowPose444 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row444_reject_checked)
theorem row444_classified : RowClassified 444 := by
  intro p generated legal
  have he : rowPose444 = p := Option.some.inj (row444_generated.symm.trans generated)
  subst p
  exact (row444_illegal legal).elim

def rowPose445 : Pose 7 := ⟨perm90, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row445_fields : pairFieldsMatchB 188160 facet0 facet390 key0 key445 rowPose445 = true := by decide +kernel
theorem row445_generated : rootPair 445 = some rowPose445 :=
  pairFieldsMatchB_sound (by decide) row445_fields
theorem row445_source : sourceKey 445 ∈ geometry.profile (sourceOwner 445) := by decide +kernel
theorem row445_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 362 key8).FastValid geometry rowPose445 := by decide +kernel
theorem row445_illegal : ¬ geometry.LegalContact rowPose445 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row445_reject_checked)
theorem row445_classified : RowClassified 445 := by
  intro p generated legal
  have he : rowPose445 = p := Option.some.inj (row445_generated.symm.trans generated)
  subst p
  exact (row445_illegal legal).elim

def rowPose446 : Pose 7 := ⟨perm87, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row446_fields : pairFieldsMatchB 188160 facet0 facet390 key0 key446 rowPose446 = true := by decide +kernel
theorem row446_generated : rootPair 446 = some rowPose446 :=
  pairFieldsMatchB_sound (by decide) row446_fields
theorem row446_source : sourceKey 446 ∈ geometry.profile (sourceOwner 446) := by decide +kernel
theorem row446_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 390 key0).FastValid geometry rowPose446 := by decide +kernel
theorem row446_illegal : ¬ geometry.LegalContact rowPose446 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row446_reject_checked)
theorem row446_classified : RowClassified 446 := by
  intro p generated legal
  have he : rowPose446 = p := Option.some.inj (row446_generated.symm.trans generated)
  subst p
  exact (row446_illegal legal).elim

def rowPose447 : Pose 7 := ⟨perm111, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row447_fields : pairFieldsMatchB 188160 facet0 facet391 key0 key447 rowPose447 = true := by decide +kernel
theorem row447_generated : rootPair 447 = some rowPose447 :=
  pairFieldsMatchB_sound (by decide) row447_fields
theorem row447_source : sourceKey 447 ∈ geometry.profile (sourceOwner 447) := by decide +kernel
theorem row447_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 391 key0).FastValid geometry rowPose447 := by decide +kernel
theorem row447_illegal : ¬ geometry.LegalContact rowPose447 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row447_reject_checked)
theorem row447_classified : RowClassified 447 := by
  intro p generated legal
  have he : rowPose447 = p := Option.some.inj (row447_generated.symm.trans generated)
  subst p
  exact (row447_illegal legal).elim

theorem chunk13_classified (i : Fin 32) : RowClassified ⟨416 + i.val, by omega⟩ := by
  fin_cases i
  · exact row416_classified
  · exact row417_classified
  · exact row418_classified
  · exact row419_classified
  · exact row420_classified
  · exact row421_classified
  · exact row422_classified
  · exact row423_classified
  · exact row424_classified
  · exact row425_classified
  · exact row426_classified
  · exact row427_classified
  · exact row428_classified
  · exact row429_classified
  · exact row430_classified
  · exact row431_classified
  · exact row432_classified
  · exact row433_classified
  · exact row434_classified
  · exact row435_classified
  · exact row436_classified
  · exact row437_classified
  · exact row438_classified
  · exact row439_classified
  · exact row440_classified
  · exact row441_classified
  · exact row442_classified
  · exact row443_classified
  · exact row444_classified
  · exact row445_classified
  · exact row446_classified
  · exact row447_classified

theorem chunk13_source (i : Fin 32) : sourceKey ⟨416 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨416 + i.val, by omega⟩) := by
  fin_cases i
  · exact row416_source
  · exact row417_source
  · exact row418_source
  · exact row419_source
  · exact row420_source
  · exact row421_source
  · exact row422_source
  · exact row423_source
  · exact row424_source
  · exact row425_source
  · exact row426_source
  · exact row427_source
  · exact row428_source
  · exact row429_source
  · exact row430_source
  · exact row431_source
  · exact row432_source
  · exact row433_source
  · exact row434_source
  · exact row435_source
  · exact row436_source
  · exact row437_source
  · exact row438_source
  · exact row439_source
  · exact row440_source
  · exact row441_source
  · exact row442_source
  · exact row443_source
  · exact row444_source
  · exact row445_source
  · exact row446_source
  · exact row447_source

#print axioms chunk13_classified
end SparseMonotiles.Contact.RootZeroPilot7
