module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose448 : Pose 7 := ⟨perm15, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row448_fields : pairFieldsMatchB 188160 facet0 facet392 key0 key448 rowPose448 = true := by decide +kernel
theorem row448_generated : rootPair 448 = some rowPose448 :=
  pairFieldsMatchB_sound (by decide) row448_fields
theorem row448_source : sourceKey 448 ∈ geometry.profile (sourceOwner 448) := by decide +kernel
theorem row448_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 392 key1).FastValid geometry rowPose448 := by decide +kernel
theorem row448_illegal : ¬ geometry.LegalContact rowPose448 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row448_reject_checked)
theorem row448_classified : RowClassified 448 := by
  intro p generated legal
  have he : rowPose448 = p := Option.some.inj (row448_generated.symm.trans generated)
  subst p
  exact (row448_illegal legal).elim

def rowPose449 : Pose 7 := ⟨perm24, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row449_fields : pairFieldsMatchB 188160 facet0 facet393 key0 key449 rowPose449 = true := by decide +kernel
theorem row449_generated : rootPair 449 = some rowPose449 :=
  pairFieldsMatchB_sound (by decide) row449_fields
theorem row449_source : sourceKey 449 ∈ geometry.profile (sourceOwner 449) := by decide +kernel
theorem row449_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 393 key1).FastValid geometry rowPose449 := by decide +kernel
theorem row449_illegal : ¬ geometry.LegalContact rowPose449 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row449_reject_checked)
theorem row449_classified : RowClassified 449 := by
  intro p generated legal
  have he : rowPose449 = p := Option.some.inj (row449_generated.symm.trans generated)
  subst p
  exact (row449_illegal legal).elim

def rowPose450 : Pose 7 := ⟨perm37, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row450_fields : pairFieldsMatchB 188160 facet0 facet394 key0 key450 rowPose450 = true := by decide +kernel
theorem row450_generated : rootPair 450 = some rowPose450 :=
  pairFieldsMatchB_sound (by decide) row450_fields
theorem row450_source : sourceKey 450 ∈ geometry.profile (sourceOwner 450) := by decide +kernel
theorem row450_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 394 key0).FastValid geometry rowPose450 := by decide +kernel
theorem row450_illegal : ¬ geometry.LegalContact rowPose450 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row450_reject_checked)
theorem row450_classified : RowClassified 450 := by
  intro p generated legal
  have he : rowPose450 = p := Option.some.inj (row450_generated.symm.trans generated)
  subst p
  exact (row450_illegal legal).elim

def rowPose451 : Pose 7 := ⟨perm42, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row451_fields : pairFieldsMatchB 188160 facet0 facet394 key0 key451 rowPose451 = true := by decide +kernel
theorem row451_generated : rootPair 451 = some rowPose451 :=
  pairFieldsMatchB_sound (by decide) row451_fields
theorem row451_source : sourceKey 451 ∈ geometry.profile (sourceOwner 451) := by decide +kernel
theorem row451_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 170 key8).FastValid geometry rowPose451 := by decide +kernel
theorem row451_illegal : ¬ geometry.LegalContact rowPose451 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row451_reject_checked)
theorem row451_classified : RowClassified 451 := by
  intro p generated legal
  have he : rowPose451 = p := Option.some.inj (row451_generated.symm.trans generated)
  subst p
  exact (row451_illegal legal).elim

def rowPose452 : Pose 7 := ⟨perm53, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row452_fields : pairFieldsMatchB 188160 facet0 facet395 key0 key452 rowPose452 = true := by decide +kernel
theorem row452_generated : rootPair 452 = some rowPose452 :=
  pairFieldsMatchB_sound (by decide) row452_fields
theorem row452_source : sourceKey 452 ∈ geometry.profile (sourceOwner 452) := by decide +kernel
theorem row452_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 395 key0).FastValid geometry rowPose452 := by decide +kernel
theorem row452_illegal : ¬ geometry.LegalContact rowPose452 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row452_reject_checked)
theorem row452_classified : RowClassified 452 := by
  intro p generated legal
  have he : rowPose452 = p := Option.some.inj (row452_generated.symm.trans generated)
  subst p
  exact (row452_illegal legal).elim

def rowPose453 : Pose 7 := ⟨perm74, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row453_fields : pairFieldsMatchB 188160 facet0 facet396 key0 key453 rowPose453 = true := by decide +kernel
theorem row453_generated : rootPair 453 = some rowPose453 :=
  pairFieldsMatchB_sound (by decide) row453_fields
theorem row453_source : sourceKey 453 ∈ geometry.profile (sourceOwner 453) := by decide +kernel
theorem row453_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 396 key0).FastValid geometry rowPose453 := by decide +kernel
theorem row453_illegal : ¬ geometry.LegalContact rowPose453 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row453_reject_checked)
theorem row453_classified : RowClassified 453 := by
  intro p generated legal
  have he : rowPose453 = p := Option.some.inj (row453_generated.symm.trans generated)
  subst p
  exact (row453_illegal legal).elim

def rowPose454 : Pose 7 := ⟨perm89, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row454_fields : pairFieldsMatchB 188160 facet0 facet397 key0 key454 rowPose454 = true := by decide +kernel
theorem row454_generated : rootPair 454 = some rowPose454 :=
  pairFieldsMatchB_sound (by decide) row454_fields
theorem row454_source : sourceKey 454 ∈ geometry.profile (sourceOwner 454) := by decide +kernel
theorem row454_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 397 key1).FastValid geometry rowPose454 := by decide +kernel
theorem row454_illegal : ¬ geometry.LegalContact rowPose454 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row454_reject_checked)
theorem row454_classified : RowClassified 454 := by
  intro p generated legal
  have he : rowPose454 = p := Option.some.inj (row454_generated.symm.trans generated)
  subst p
  exact (row454_illegal legal).elim

def rowPose455 : Pose 7 := ⟨perm101, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row455_fields : pairFieldsMatchB 188160 facet0 facet398 key0 key455 rowPose455 = true := by decide +kernel
theorem row455_generated : rootPair 455 = some rowPose455 :=
  pairFieldsMatchB_sound (by decide) row455_fields
theorem row455_source : sourceKey 455 ∈ geometry.profile (sourceOwner 455) := by decide +kernel
theorem row455_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 398 key0).FastValid geometry rowPose455 := by decide +kernel
theorem row455_illegal : ¬ geometry.LegalContact rowPose455 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row455_reject_checked)
theorem row455_classified : RowClassified 455 := by
  intro p generated legal
  have he : rowPose455 = p := Option.some.inj (row455_generated.symm.trans generated)
  subst p
  exact (row455_illegal legal).elim

def rowPose456 : Pose 7 := ⟨perm5, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row456_fields : pairFieldsMatchB 188160 facet0 facet399 key0 key456 rowPose456 = true := by decide +kernel
theorem row456_generated : rootPair 456 = some rowPose456 :=
  pairFieldsMatchB_sound (by decide) row456_fields
theorem row456_source : sourceKey 456 ∈ geometry.profile (sourceOwner 456) := by decide +kernel
theorem row456_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 399 key1).FastValid geometry rowPose456 := by decide +kernel
theorem row456_illegal : ¬ geometry.LegalContact rowPose456 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row456_reject_checked)
theorem row456_classified : RowClassified 456 := by
  intro p generated legal
  have he : rowPose456 = p := Option.some.inj (row456_generated.symm.trans generated)
  subst p
  exact (row456_illegal legal).elim

def rowPose457 : Pose 7 := ⟨perm21, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row457_fields : pairFieldsMatchB 188160 facet0 facet400 key0 key457 rowPose457 = true := by decide +kernel
theorem row457_generated : rootPair 457 = some rowPose457 :=
  pairFieldsMatchB_sound (by decide) row457_fields
theorem row457_source : sourceKey 457 ∈ geometry.profile (sourceOwner 457) := by decide +kernel
theorem row457_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 400 key0).FastValid geometry rowPose457 := by decide +kernel
theorem row457_illegal : ¬ geometry.LegalContact rowPose457 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row457_reject_checked)
theorem row457_classified : RowClassified 457 := by
  intro p generated legal
  have he : rowPose457 = p := Option.some.inj (row457_generated.symm.trans generated)
  subst p
  exact (row457_illegal legal).elim

def rowPose458 : Pose 7 := ⟨perm42, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row458_fields : pairFieldsMatchB 188160 facet0 facet401 key0 key458 rowPose458 = true := by decide +kernel
theorem row458_generated : rootPair 458 = some rowPose458 :=
  pairFieldsMatchB_sound (by decide) row458_fields
theorem row458_source : sourceKey 458 ∈ geometry.profile (sourceOwner 458) := by decide +kernel
theorem row458_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 401 key0).FastValid geometry rowPose458 := by decide +kernel
theorem row458_illegal : ¬ geometry.LegalContact rowPose458 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row458_reject_checked)
theorem row458_classified : RowClassified 458 := by
  intro p generated legal
  have he : rowPose458 = p := Option.some.inj (row458_generated.symm.trans generated)
  subst p
  exact (row458_illegal legal).elim

def rowPose459 : Pose 7 := ⟨perm53, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row459_fields : pairFieldsMatchB 188160 facet0 facet402 key0 key459 rowPose459 = true := by decide +kernel
theorem row459_generated : rootPair 459 = some rowPose459 :=
  pairFieldsMatchB_sound (by decide) row459_fields
theorem row459_source : sourceKey 459 ∈ geometry.profile (sourceOwner 459) := by decide +kernel
theorem row459_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 430 key8).FastValid geometry rowPose459 := by decide +kernel
theorem row459_illegal : ¬ geometry.LegalContact rowPose459 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row459_reject_checked)
theorem row459_classified : RowClassified 459 := by
  intro p generated legal
  have he : rowPose459 = p := Option.some.inj (row459_generated.symm.trans generated)
  subst p
  exact (row459_illegal legal).elim

def rowPose460 : Pose 7 := ⟨perm58, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row460_fields : pairFieldsMatchB 188160 facet0 facet402 key0 key460 rowPose460 = true := by decide +kernel
theorem row460_generated : rootPair 460 = some rowPose460 :=
  pairFieldsMatchB_sound (by decide) row460_fields
theorem row460_source : sourceKey 460 ∈ geometry.profile (sourceOwner 460) := by decide +kernel
theorem row460_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 402 key0).FastValid geometry rowPose460 := by decide +kernel
theorem row460_illegal : ¬ geometry.LegalContact rowPose460 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row460_reject_checked)
theorem row460_classified : RowClassified 460 := by
  intro p generated legal
  have he : rowPose460 = p := Option.some.inj (row460_generated.symm.trans generated)
  subst p
  exact (row460_illegal legal).elim

def rowPose461 : Pose 7 := ⟨perm69, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row461_fields : pairFieldsMatchB 188160 facet0 facet403 key0 key461 rowPose461 = true := by decide +kernel
theorem row461_generated : rootPair 461 = some rowPose461 :=
  pairFieldsMatchB_sound (by decide) row461_fields
theorem row461_source : sourceKey 461 ∈ geometry.profile (sourceOwner 461) := by decide +kernel
theorem row461_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 403 key1).FastValid geometry rowPose461 := by decide +kernel
theorem row461_illegal : ¬ geometry.LegalContact rowPose461 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row461_reject_checked)
theorem row461_classified : RowClassified 461 := by
  intro p generated legal
  have he : rowPose461 = p := Option.some.inj (row461_generated.symm.trans generated)
  subst p
  exact (row461_illegal legal).elim

def rowPose462 : Pose 7 := ⟨perm90, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row462_fields : pairFieldsMatchB 188160 facet0 facet404 key0 key462 rowPose462 = true := by decide +kernel
theorem row462_generated : rootPair 462 = some rowPose462 :=
  pairFieldsMatchB_sound (by decide) row462_fields
theorem row462_source : sourceKey 462 ∈ geometry.profile (sourceOwner 462) := by decide +kernel
theorem row462_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 404 key1).FastValid geometry rowPose462 := by decide +kernel
theorem row462_illegal : ¬ geometry.LegalContact rowPose462 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row462_reject_checked)
theorem row462_classified : RowClassified 462 := by
  intro p generated legal
  have he : rowPose462 = p := Option.some.inj (row462_generated.symm.trans generated)
  subst p
  exact (row462_illegal legal).elim

def rowPose463 : Pose 7 := ⟨perm106, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row463_fields : pairFieldsMatchB 188160 facet0 facet405 key0 key463 rowPose463 = true := by decide +kernel
theorem row463_generated : rootPair 463 = some rowPose463 :=
  pairFieldsMatchB_sound (by decide) row463_fields
theorem row463_source : sourceKey 463 ∈ geometry.profile (sourceOwner 463) := by decide +kernel
theorem row463_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 405 key0).FastValid geometry rowPose463 := by decide +kernel
theorem row463_illegal : ¬ geometry.LegalContact rowPose463 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row463_reject_checked)
theorem row463_classified : RowClassified 463 := by
  intro p generated legal
  have he : rowPose463 = p := Option.some.inj (row463_generated.symm.trans generated)
  subst p
  exact (row463_illegal legal).elim

def rowPose464 : Pose 7 := ⟨perm0, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row464_fields : pairFieldsMatchB 188160 facet0 facet406 key0 key464 rowPose464 = true := by decide +kernel
theorem row464_generated : rootPair 464 = some rowPose464 :=
  pairFieldsMatchB_sound (by decide) row464_fields
theorem row464_source : sourceKey 464 ∈ geometry.profile (sourceOwner 464) := by decide +kernel
theorem row464_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 406 key0).FastValid geometry rowPose464 := by decide +kernel
theorem row464_illegal : ¬ geometry.LegalContact rowPose464 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row464_reject_checked)
theorem row464_classified : RowClassified 464 := by
  intro p generated legal
  have he : rowPose464 = p := Option.some.inj (row464_generated.symm.trans generated)
  subst p
  exact (row464_illegal legal).elim

def rowPose465 : Pose 7 := ⟨perm21, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row465_fields : pairFieldsMatchB 188160 facet0 facet407 key0 key465 rowPose465 = true := by decide +kernel
theorem row465_generated : rootPair 465 = some rowPose465 :=
  pairFieldsMatchB_sound (by decide) row465_fields
theorem row465_source : sourceKey 465 ∈ geometry.profile (sourceOwner 465) := by decide +kernel
theorem row465_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 295 key8).FastValid geometry rowPose465 := by decide +kernel
theorem row465_illegal : ¬ geometry.LegalContact rowPose465 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row465_reject_checked)
theorem row465_classified : RowClassified 465 := by
  intro p generated legal
  have he : rowPose465 = p := Option.some.inj (row465_generated.symm.trans generated)
  subst p
  exact (row465_illegal legal).elim

def rowPose466 : Pose 7 := ⟨perm24, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row466_fields : pairFieldsMatchB 188160 facet0 facet407 key0 key466 rowPose466 = true := by decide +kernel
theorem row466_generated : rootPair 466 = some rowPose466 :=
  pairFieldsMatchB_sound (by decide) row466_fields
theorem row466_source : sourceKey 466 ∈ geometry.profile (sourceOwner 466) := by decide +kernel
theorem row466_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 407 key0).FastValid geometry rowPose466 := by decide +kernel
theorem row466_illegal : ¬ geometry.LegalContact rowPose466 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row466_reject_checked)
theorem row466_classified : RowClassified 466 := by
  intro p generated legal
  have he : rowPose466 = p := Option.some.inj (row466_generated.symm.trans generated)
  subst p
  exact (row466_illegal legal).elim

def rowPose467 : Pose 7 := ⟨perm37, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row467_fields : pairFieldsMatchB 188160 facet0 facet408 key0 key467 rowPose467 = true := by decide +kernel
theorem row467_generated : rootPair 467 = some rowPose467 :=
  pairFieldsMatchB_sound (by decide) row467_fields
theorem row467_source : sourceKey 467 ∈ geometry.profile (sourceOwner 467) := by decide +kernel
theorem row467_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 408 key1).FastValid geometry rowPose467 := by decide +kernel
theorem row467_illegal : ¬ geometry.LegalContact rowPose467 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row467_reject_checked)
theorem row467_classified : RowClassified 467 := by
  intro p generated legal
  have he : rowPose467 = p := Option.some.inj (row467_generated.symm.trans generated)
  subst p
  exact (row467_illegal legal).elim

def rowPose468 : Pose 7 := ⟨perm58, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row468_fields : pairFieldsMatchB 188160 facet0 facet409 key0 key468 rowPose468 = true := by decide +kernel
theorem row468_generated : rootPair 468 = some rowPose468 :=
  pairFieldsMatchB_sound (by decide) row468_fields
theorem row468_source : sourceKey 468 ∈ geometry.profile (sourceOwner 468) := by decide +kernel
theorem row468_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 409 key1).FastValid geometry rowPose468 := by decide +kernel
theorem row468_illegal : ¬ geometry.LegalContact rowPose468 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row468_reject_checked)
theorem row468_classified : RowClassified 468 := by
  intro p generated legal
  have he : rowPose468 = p := Option.some.inj (row468_generated.symm.trans generated)
  subst p
  exact (row468_illegal legal).elim

def rowPose469 : Pose 7 := ⟨perm71, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row469_fields : pairFieldsMatchB 188160 facet0 facet410 key0 key469 rowPose469 = true := by decide +kernel
theorem row469_generated : rootPair 469 = some rowPose469 :=
  pairFieldsMatchB_sound (by decide) row469_fields
theorem row469_source : sourceKey 469 ∈ geometry.profile (sourceOwner 469) := by decide +kernel
theorem row469_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 410 key0).FastValid geometry rowPose469 := by decide +kernel
theorem row469_illegal : ¬ geometry.LegalContact rowPose469 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row469_reject_checked)
theorem row469_classified : RowClassified 469 := by
  intro p generated legal
  have he : rowPose469 = p := Option.some.inj (row469_generated.symm.trans generated)
  subst p
  exact (row469_illegal legal).elim

def rowPose470 : Pose 7 := ⟨perm95, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row470_fields : pairFieldsMatchB 188160 facet0 facet411 key0 key470 rowPose470 = true := by decide +kernel
theorem row470_generated : rootPair 470 = some rowPose470 :=
  pairFieldsMatchB_sound (by decide) row470_fields
theorem row470_source : sourceKey 470 ∈ geometry.profile (sourceOwner 470) := by decide +kernel
theorem row470_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 411 key1).FastValid geometry rowPose470 := by decide +kernel
theorem row470_illegal : ¬ geometry.LegalContact rowPose470 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row470_reject_checked)
theorem row470_classified : RowClassified 470 := by
  intro p generated legal
  have he : rowPose470 = p := Option.some.inj (row470_generated.symm.trans generated)
  subst p
  exact (row470_illegal legal).elim

def rowPose471 : Pose 7 := ⟨perm111, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row471_fields : pairFieldsMatchB 188160 facet0 facet412 key0 key471 rowPose471 = true := by decide +kernel
theorem row471_generated : rootPair 471 = some rowPose471 :=
  pairFieldsMatchB_sound (by decide) row471_fields
theorem row471_source : sourceKey 471 ∈ geometry.profile (sourceOwner 471) := by decide +kernel
theorem row471_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 412 key0).FastValid geometry rowPose471 := by decide +kernel
theorem row471_illegal : ¬ geometry.LegalContact rowPose471 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row471_reject_checked)
theorem row471_classified : RowClassified 471 := by
  intro p generated legal
  have he : rowPose471 = p := Option.some.inj (row471_generated.symm.trans generated)
  subst p
  exact (row471_illegal legal).elim

def rowPose472 : Pose 7 := ⟨perm15, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row472_fields : pairFieldsMatchB 188160 facet0 facet413 key0 key472 rowPose472 = true := by decide +kernel
theorem row472_generated : rootPair 472 = some rowPose472 :=
  pairFieldsMatchB_sound (by decide) row472_fields
theorem row472_source : sourceKey 472 ∈ geometry.profile (sourceOwner 472) := by decide +kernel
theorem row472_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 413 key1).FastValid geometry rowPose472 := by decide +kernel
theorem row472_illegal : ¬ geometry.LegalContact rowPose472 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row472_reject_checked)
theorem row472_classified : RowClassified 472 := by
  intro p generated legal
  have he : rowPose472 = p := Option.some.inj (row472_generated.symm.trans generated)
  subst p
  exact (row472_illegal legal).elim

def rowPose473 : Pose 7 := ⟨perm24, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row473_fields : pairFieldsMatchB 188160 facet0 facet414 key0 key473 rowPose473 = true := by decide +kernel
theorem row473_generated : rootPair 473 = some rowPose473 :=
  pairFieldsMatchB_sound (by decide) row473_fields
theorem row473_source : sourceKey 473 ∈ geometry.profile (sourceOwner 473) := by decide +kernel
theorem row473_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 414 key1).FastValid geometry rowPose473 := by decide +kernel
theorem row473_illegal : ¬ geometry.LegalContact rowPose473 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row473_reject_checked)
theorem row473_classified : RowClassified 473 := by
  intro p generated legal
  have he : rowPose473 = p := Option.some.inj (row473_generated.symm.trans generated)
  subst p
  exact (row473_illegal legal).elim

def rowPose474 : Pose 7 := ⟨perm37, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row474_fields : pairFieldsMatchB 188160 facet0 facet415 key0 key474 rowPose474 = true := by decide +kernel
theorem row474_generated : rootPair 474 = some rowPose474 :=
  pairFieldsMatchB_sound (by decide) row474_fields
theorem row474_source : sourceKey 474 ∈ geometry.profile (sourceOwner 474) := by decide +kernel
theorem row474_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 415 key0).FastValid geometry rowPose474 := by decide +kernel
theorem row474_illegal : ¬ geometry.LegalContact rowPose474 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row474_reject_checked)
theorem row474_classified : RowClassified 474 := by
  intro p generated legal
  have he : rowPose474 = p := Option.some.inj (row474_generated.symm.trans generated)
  subst p
  exact (row474_illegal legal).elim

def rowPose475 : Pose 7 := ⟨perm42, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row475_fields : pairFieldsMatchB 188160 facet0 facet415 key0 key475 rowPose475 = true := by decide +kernel
theorem row475_generated : rootPair 475 = some rowPose475 :=
  pairFieldsMatchB_sound (by decide) row475_fields
theorem row475_source : sourceKey 475 ∈ geometry.profile (sourceOwner 475) := by decide +kernel
theorem row475_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 191 key8).FastValid geometry rowPose475 := by decide +kernel
theorem row475_illegal : ¬ geometry.LegalContact rowPose475 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row475_reject_checked)
theorem row475_classified : RowClassified 475 := by
  intro p generated legal
  have he : rowPose475 = p := Option.some.inj (row475_generated.symm.trans generated)
  subst p
  exact (row475_illegal legal).elim

def rowPose476 : Pose 7 := ⟨perm53, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row476_fields : pairFieldsMatchB 188160 facet0 facet416 key0 key476 rowPose476 = true := by decide +kernel
theorem row476_generated : rootPair 476 = some rowPose476 :=
  pairFieldsMatchB_sound (by decide) row476_fields
theorem row476_source : sourceKey 476 ∈ geometry.profile (sourceOwner 476) := by decide +kernel
theorem row476_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 416 key0).FastValid geometry rowPose476 := by decide +kernel
theorem row476_illegal : ¬ geometry.LegalContact rowPose476 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row476_reject_checked)
theorem row476_classified : RowClassified 476 := by
  intro p generated legal
  have he : rowPose476 = p := Option.some.inj (row476_generated.symm.trans generated)
  subst p
  exact (row476_illegal legal).elim

def rowPose477 : Pose 7 := ⟨perm74, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row477_fields : pairFieldsMatchB 188160 facet0 facet417 key0 key477 rowPose477 = true := by decide +kernel
theorem row477_generated : rootPair 477 = some rowPose477 :=
  pairFieldsMatchB_sound (by decide) row477_fields
theorem row477_source : sourceKey 477 ∈ geometry.profile (sourceOwner 477) := by decide +kernel
theorem row477_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 417 key0).FastValid geometry rowPose477 := by decide +kernel
theorem row477_illegal : ¬ geometry.LegalContact rowPose477 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row477_reject_checked)
theorem row477_classified : RowClassified 477 := by
  intro p generated legal
  have he : rowPose477 = p := Option.some.inj (row477_generated.symm.trans generated)
  subst p
  exact (row477_illegal legal).elim

def rowPose478 : Pose 7 := ⟨perm89, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row478_fields : pairFieldsMatchB 188160 facet0 facet418 key0 key478 rowPose478 = true := by decide +kernel
theorem row478_generated : rootPair 478 = some rowPose478 :=
  pairFieldsMatchB_sound (by decide) row478_fields
theorem row478_source : sourceKey 478 ∈ geometry.profile (sourceOwner 478) := by decide +kernel
theorem row478_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 418 key1).FastValid geometry rowPose478 := by decide +kernel
theorem row478_illegal : ¬ geometry.LegalContact rowPose478 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row478_reject_checked)
theorem row478_classified : RowClassified 478 := by
  intro p generated legal
  have he : rowPose478 = p := Option.some.inj (row478_generated.symm.trans generated)
  subst p
  exact (row478_illegal legal).elim

def rowPose479 : Pose 7 := ⟨perm101, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row479_fields : pairFieldsMatchB 188160 facet0 facet419 key0 key479 rowPose479 = true := by decide +kernel
theorem row479_generated : rootPair 479 = some rowPose479 :=
  pairFieldsMatchB_sound (by decide) row479_fields
theorem row479_source : sourceKey 479 ∈ geometry.profile (sourceOwner 479) := by decide +kernel
theorem row479_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 419 key0).FastValid geometry rowPose479 := by decide +kernel
theorem row479_illegal : ¬ geometry.LegalContact rowPose479 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row479_reject_checked)
theorem row479_classified : RowClassified 479 := by
  intro p generated legal
  have he : rowPose479 = p := Option.some.inj (row479_generated.symm.trans generated)
  subst p
  exact (row479_illegal legal).elim

theorem chunk14_classified (i : Fin 32) : RowClassified ⟨448 + i.val, by omega⟩ := by
  fin_cases i
  · exact row448_classified
  · exact row449_classified
  · exact row450_classified
  · exact row451_classified
  · exact row452_classified
  · exact row453_classified
  · exact row454_classified
  · exact row455_classified
  · exact row456_classified
  · exact row457_classified
  · exact row458_classified
  · exact row459_classified
  · exact row460_classified
  · exact row461_classified
  · exact row462_classified
  · exact row463_classified
  · exact row464_classified
  · exact row465_classified
  · exact row466_classified
  · exact row467_classified
  · exact row468_classified
  · exact row469_classified
  · exact row470_classified
  · exact row471_classified
  · exact row472_classified
  · exact row473_classified
  · exact row474_classified
  · exact row475_classified
  · exact row476_classified
  · exact row477_classified
  · exact row478_classified
  · exact row479_classified

theorem chunk14_source (i : Fin 32) : sourceKey ⟨448 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨448 + i.val, by omega⟩) := by
  fin_cases i
  · exact row448_source
  · exact row449_source
  · exact row450_source
  · exact row451_source
  · exact row452_source
  · exact row453_source
  · exact row454_source
  · exact row455_source
  · exact row456_source
  · exact row457_source
  · exact row458_source
  · exact row459_source
  · exact row460_source
  · exact row461_source
  · exact row462_source
  · exact row463_source
  · exact row464_source
  · exact row465_source
  · exact row466_source
  · exact row467_source
  · exact row468_source
  · exact row469_source
  · exact row470_source
  · exact row471_source
  · exact row472_source
  · exact row473_source
  · exact row474_source
  · exact row475_source
  · exact row476_source
  · exact row477_source
  · exact row478_source
  · exact row479_source

#print axioms chunk14_classified
end SparseMonotiles.Contact.RootZeroPilot7
