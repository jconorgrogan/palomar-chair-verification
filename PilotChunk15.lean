module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose480 : Pose 7 := ⟨perm15, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row480_fields : pairFieldsMatchB 188160 facet0 facet420 key0 key480 rowPose480 = true := by decide +kernel
theorem row480_generated : rootPair 480 = some rowPose480 :=
  pairFieldsMatchB_sound (by decide) row480_fields
theorem row480_source : sourceKey 480 ∈ geometry.profile (sourceOwner 480) := by decide +kernel
theorem row480_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 420 key1).FastValid geometry rowPose480 := by decide +kernel
theorem row480_illegal : ¬ geometry.LegalContact rowPose480 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row480_reject_checked)
theorem row480_classified : RowClassified 480 := by
  intro p generated legal
  have he : rowPose480 = p := Option.some.inj (row480_generated.symm.trans generated)
  subst p
  exact (row480_illegal legal).elim

def rowPose481 : Pose 7 := ⟨perm24, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row481_fields : pairFieldsMatchB 188160 facet0 facet421 key0 key481 rowPose481 = true := by decide +kernel
theorem row481_generated : rootPair 481 = some rowPose481 :=
  pairFieldsMatchB_sound (by decide) row481_fields
theorem row481_source : sourceKey 481 ∈ geometry.profile (sourceOwner 481) := by decide +kernel
theorem row481_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 421 key1).FastValid geometry rowPose481 := by decide +kernel
theorem row481_illegal : ¬ geometry.LegalContact rowPose481 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row481_reject_checked)
theorem row481_classified : RowClassified 481 := by
  intro p generated legal
  have he : rowPose481 = p := Option.some.inj (row481_generated.symm.trans generated)
  subst p
  exact (row481_illegal legal).elim

def rowPose482 : Pose 7 := ⟨perm38, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row482_fields : pairFieldsMatchB 188160 facet0 facet422 key0 key482 rowPose482 = true := by decide +kernel
theorem row482_generated : rootPair 482 = some rowPose482 :=
  pairFieldsMatchB_sound (by decide) row482_fields
theorem row482_source : sourceKey 482 ∈ geometry.profile (sourceOwner 482) := by decide +kernel
theorem row482_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 422 key0).FastValid geometry rowPose482 := by decide +kernel
theorem row482_illegal : ¬ geometry.LegalContact rowPose482 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row482_reject_checked)
theorem row482_classified : RowClassified 482 := by
  intro p generated legal
  have he : rowPose482 = p := Option.some.inj (row482_generated.symm.trans generated)
  subst p
  exact (row482_illegal legal).elim

def rowPose483 : Pose 7 := ⟨perm56, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row483_fields : pairFieldsMatchB 188160 facet0 facet423 key0 key483 rowPose483 = true := by decide +kernel
theorem row483_generated : rootPair 483 = some rowPose483 :=
  pairFieldsMatchB_sound (by decide) row483_fields
theorem row483_source : sourceKey 483 ∈ geometry.profile (sourceOwner 483) := by decide +kernel
theorem row483_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 423 key1).FastValid geometry rowPose483 := by decide +kernel
theorem row483_illegal : ¬ geometry.LegalContact rowPose483 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row483_reject_checked)
theorem row483_classified : RowClassified 483 := by
  intro p generated legal
  have he : rowPose483 = p := Option.some.inj (row483_generated.symm.trans generated)
  subst p
  exact (row483_illegal legal).elim

def rowPose484 : Pose 7 := ⟨perm69, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row484_fields : pairFieldsMatchB 188160 facet0 facet424 key0 key484 rowPose484 = true := by decide +kernel
theorem row484_generated : rootPair 484 = some rowPose484 :=
  pairFieldsMatchB_sound (by decide) row484_fields
theorem row484_source : sourceKey 484 ∈ geometry.profile (sourceOwner 484) := by decide +kernel
theorem row484_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 424 key0).FastValid geometry rowPose484 := by decide +kernel
theorem row484_illegal : ¬ geometry.LegalContact rowPose484 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row484_reject_checked)
theorem row484_classified : RowClassified 484 := by
  intro p generated legal
  have he : rowPose484 = p := Option.some.inj (row484_generated.symm.trans generated)
  subst p
  exact (row484_illegal legal).elim

def rowPose485 : Pose 7 := ⟨perm90, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row485_fields : pairFieldsMatchB 188160 facet0 facet425 key0 key485 rowPose485 = true := by decide +kernel
theorem row485_generated : rootPair 485 = some rowPose485 :=
  pairFieldsMatchB_sound (by decide) row485_fields
theorem row485_source : sourceKey 485 ∈ geometry.profile (sourceOwner 485) := by decide +kernel
theorem row485_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 425 key0).FastValid geometry rowPose485 := by decide +kernel
theorem row485_illegal : ¬ geometry.LegalContact rowPose485 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row485_reject_checked)
theorem row485_classified : RowClassified 485 := by
  intro p generated legal
  have he : rowPose485 = p := Option.some.inj (row485_generated.symm.trans generated)
  subst p
  exact (row485_illegal legal).elim

def rowPose486 : Pose 7 := ⟨perm96, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row486_fields : pairFieldsMatchB 188160 facet0 facet426 key0 key486 rowPose486 = true := by decide +kernel
theorem row486_generated : rootPair 486 = some rowPose486 :=
  pairFieldsMatchB_sound (by decide) row486_fields
theorem row486_source : sourceKey 486 ∈ geometry.profile (sourceOwner 486) := by decide +kernel
theorem row486_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 426 key0).FastValid geometry rowPose486 := by decide +kernel
theorem row486_illegal : ¬ geometry.LegalContact rowPose486 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row486_reject_checked)
theorem row486_classified : RowClassified 486 := by
  intro p generated legal
  have he : rowPose486 = p := Option.some.inj (row486_generated.symm.trans generated)
  subst p
  exact (row486_illegal legal).elim

def rowPose487 : Pose 7 := ⟨perm111, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row487_fields : pairFieldsMatchB 188160 facet0 facet426 key0 key487 rowPose487 = true := by decide +kernel
theorem row487_generated : rootPair 487 = some rowPose487 :=
  pairFieldsMatchB_sound (by decide) row487_fields
theorem row487_source : sourceKey 487 ∈ geometry.profile (sourceOwner 487) := by decide +kernel
theorem row487_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 879 key8).FastValid geometry rowPose487 := by decide +kernel
theorem row487_illegal : ¬ geometry.LegalContact rowPose487 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row487_reject_checked)
theorem row487_classified : RowClassified 487 := by
  intro p generated legal
  have he : rowPose487 = p := Option.some.inj (row487_generated.symm.trans generated)
  subst p
  exact (row487_illegal legal).elim

def rowPose488 : Pose 7 := ⟨perm15, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row488_fields : pairFieldsMatchB 188160 facet0 facet427 key0 key488 rowPose488 = true := by decide +kernel
theorem row488_generated : rootPair 488 = some rowPose488 :=
  pairFieldsMatchB_sound (by decide) row488_fields
theorem row488_source : sourceKey 488 ∈ geometry.profile (sourceOwner 488) := by decide +kernel
theorem row488_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 427 key0).FastValid geometry rowPose488 := by decide +kernel
theorem row488_illegal : ¬ geometry.LegalContact rowPose488 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row488_reject_checked)
theorem row488_classified : RowClassified 488 := by
  intro p generated legal
  have he : rowPose488 = p := Option.some.inj (row488_generated.symm.trans generated)
  subst p
  exact (row488_illegal legal).elim

def rowPose489 : Pose 7 := ⟨perm24, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row489_fields : pairFieldsMatchB 188160 facet0 facet428 key0 key489 rowPose489 = true := by decide +kernel
theorem row489_generated : rootPair 489 = some rowPose489 :=
  pairFieldsMatchB_sound (by decide) row489_fields
theorem row489_source : sourceKey 489 ∈ geometry.profile (sourceOwner 489) := by decide +kernel
theorem row489_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 428 key0).FastValid geometry rowPose489 := by decide +kernel
theorem row489_illegal : ¬ geometry.LegalContact rowPose489 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row489_reject_checked)
theorem row489_classified : RowClassified 489 := by
  intro p generated legal
  have he : rowPose489 = p := Option.some.inj (row489_generated.symm.trans generated)
  subst p
  exact (row489_illegal legal).elim

def rowPose490 : Pose 7 := ⟨perm38, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row490_fields : pairFieldsMatchB 188160 facet0 facet429 key0 key490 rowPose490 = true := by decide +kernel
theorem row490_generated : rootPair 490 = some rowPose490 :=
  pairFieldsMatchB_sound (by decide) row490_fields
theorem row490_source : sourceKey 490 ∈ geometry.profile (sourceOwner 490) := by decide +kernel
theorem row490_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 429 key1).FastValid geometry rowPose490 := by decide +kernel
theorem row490_illegal : ¬ geometry.LegalContact rowPose490 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row490_reject_checked)
theorem row490_classified : RowClassified 490 := by
  intro p generated legal
  have he : rowPose490 = p := Option.some.inj (row490_generated.symm.trans generated)
  subst p
  exact (row490_illegal legal).elim

def rowPose491 : Pose 7 := ⟨perm56, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row491_fields : pairFieldsMatchB 188160 facet0 facet430 key0 key491 rowPose491 = true := by decide +kernel
theorem row491_generated : rootPair 491 = some rowPose491 :=
  pairFieldsMatchB_sound (by decide) row491_fields
theorem row491_source : sourceKey 491 ∈ geometry.profile (sourceOwner 491) := by decide +kernel
theorem row491_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 430 key0).FastValid geometry rowPose491 := by decide +kernel
theorem row491_illegal : ¬ geometry.LegalContact rowPose491 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row491_reject_checked)
theorem row491_classified : RowClassified 491 := by
  intro p generated legal
  have he : rowPose491 = p := Option.some.inj (row491_generated.symm.trans generated)
  subst p
  exact (row491_illegal legal).elim

def rowPose492 : Pose 7 := ⟨perm69, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row492_fields : pairFieldsMatchB 188160 facet0 facet431 key0 key492 rowPose492 = true := by decide +kernel
theorem row492_generated : rootPair 492 = some rowPose492 :=
  pairFieldsMatchB_sound (by decide) row492_fields
theorem row492_source : sourceKey 492 ∈ geometry.profile (sourceOwner 492) := by decide +kernel
theorem row492_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 431 key1).FastValid geometry rowPose492 := by decide +kernel
theorem row492_illegal : ¬ geometry.LegalContact rowPose492 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row492_reject_checked)
theorem row492_classified : RowClassified 492 := by
  intro p generated legal
  have he : rowPose492 = p := Option.some.inj (row492_generated.symm.trans generated)
  subst p
  exact (row492_illegal legal).elim

def rowPose493 : Pose 7 := ⟨perm90, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row493_fields : pairFieldsMatchB 188160 facet0 facet432 key0 key493 rowPose493 = true := by decide +kernel
theorem row493_generated : rootPair 493 = some rowPose493 :=
  pairFieldsMatchB_sound (by decide) row493_fields
theorem row493_source : sourceKey 493 ∈ geometry.profile (sourceOwner 493) := by decide +kernel
theorem row493_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 432 key1).FastValid geometry rowPose493 := by decide +kernel
theorem row493_illegal : ¬ geometry.LegalContact rowPose493 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row493_reject_checked)
theorem row493_classified : RowClassified 493 := by
  intro p generated legal
  have he : rowPose493 = p := Option.some.inj (row493_generated.symm.trans generated)
  subst p
  exact (row493_illegal legal).elim

def rowPose494 : Pose 7 := ⟨perm96, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row494_fields : pairFieldsMatchB 188160 facet0 facet433 key0 key494 rowPose494 = true := by decide +kernel
theorem row494_generated : rootPair 494 = some rowPose494 :=
  pairFieldsMatchB_sound (by decide) row494_fields
theorem row494_source : sourceKey 494 ∈ geometry.profile (sourceOwner 494) := by decide +kernel
theorem row494_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 448 key8).FastValid geometry rowPose494 := by decide +kernel
theorem row494_illegal : ¬ geometry.LegalContact rowPose494 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row494_reject_checked)
theorem row494_classified : RowClassified 494 := by
  intro p generated legal
  have he : rowPose494 = p := Option.some.inj (row494_generated.symm.trans generated)
  subst p
  exact (row494_illegal legal).elim

def rowPose495 : Pose 7 := ⟨perm111, ![false, false, true, true, true, true, false], ![-2, 0, 2, 2, 2, 2, 0]⟩
theorem row495_fields : pairFieldsMatchB 188160 facet0 facet433 key0 key495 rowPose495 = true := by decide +kernel
theorem row495_generated : rootPair 495 = some rowPose495 :=
  pairFieldsMatchB_sound (by decide) row495_fields
theorem row495_source : sourceKey 495 ∈ geometry.profile (sourceOwner 495) := by decide +kernel
theorem row495_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 433 key0).FastValid geometry rowPose495 := by decide +kernel
theorem row495_illegal : ¬ geometry.LegalContact rowPose495 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row495_reject_checked)
theorem row495_classified : RowClassified 495 := by
  intro p generated legal
  have he : rowPose495 = p := Option.some.inj (row495_generated.symm.trans generated)
  subst p
  exact (row495_illegal legal).elim

def rowPose496 : Pose 7 := ⟨perm5, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row496_fields : pairFieldsMatchB 188160 facet0 facet434 key0 key496 rowPose496 = true := by decide +kernel
theorem row496_generated : rootPair 496 = some rowPose496 :=
  pairFieldsMatchB_sound (by decide) row496_fields
theorem row496_source : sourceKey 496 ∈ geometry.profile (sourceOwner 496) := by decide +kernel
theorem row496_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 434 key0).FastValid geometry rowPose496 := by decide +kernel
theorem row496_illegal : ¬ geometry.LegalContact rowPose496 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row496_reject_checked)
theorem row496_classified : RowClassified 496 := by
  intro p generated legal
  have he : rowPose496 = p := Option.some.inj (row496_generated.symm.trans generated)
  subst p
  exact (row496_illegal legal).elim

def rowPose497 : Pose 7 := ⟨perm21, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row497_fields : pairFieldsMatchB 188160 facet0 facet435 key0 key497 rowPose497 = true := by decide +kernel
theorem row497_generated : rootPair 497 = some rowPose497 :=
  pairFieldsMatchB_sound (by decide) row497_fields
theorem row497_source : sourceKey 497 ∈ geometry.profile (sourceOwner 497) := by decide +kernel
theorem row497_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 435 key1).FastValid geometry rowPose497 := by decide +kernel
theorem row497_illegal : ¬ geometry.LegalContact rowPose497 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row497_reject_checked)
theorem row497_classified : RowClassified 497 := by
  intro p generated legal
  have he : rowPose497 = p := Option.some.inj (row497_generated.symm.trans generated)
  subst p
  exact (row497_illegal legal).elim

def rowPose498 : Pose 7 := ⟨perm42, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row498_fields : pairFieldsMatchB 188160 facet0 facet436 key0 key498 rowPose498 = true := by decide +kernel
theorem row498_generated : rootPair 498 = some rowPose498 :=
  pairFieldsMatchB_sound (by decide) row498_fields
theorem row498_source : sourceKey 498 ∈ geometry.profile (sourceOwner 498) := by decide +kernel
theorem row498_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 436 key1).FastValid geometry rowPose498 := by decide +kernel
theorem row498_illegal : ¬ geometry.LegalContact rowPose498 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row498_reject_checked)
theorem row498_classified : RowClassified 498 := by
  intro p generated legal
  have he : rowPose498 = p := Option.some.inj (row498_generated.symm.trans generated)
  subst p
  exact (row498_illegal legal).elim

def rowPose499 : Pose 7 := ⟨perm53, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row499_fields : pairFieldsMatchB 188160 facet0 facet437 key0 key499 rowPose499 = true := by decide +kernel
theorem row499_generated : rootPair 499 = some rowPose499 :=
  pairFieldsMatchB_sound (by decide) row499_fields
theorem row499_source : sourceKey 499 ∈ geometry.profile (sourceOwner 499) := by decide +kernel
theorem row499_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 437 key0).FastValid geometry rowPose499 := by decide +kernel
theorem row499_illegal : ¬ geometry.LegalContact rowPose499 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row499_reject_checked)
theorem row499_classified : RowClassified 499 := by
  intro p generated legal
  have he : rowPose499 = p := Option.some.inj (row499_generated.symm.trans generated)
  subst p
  exact (row499_illegal legal).elim

def rowPose500 : Pose 7 := ⟨perm58, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row500_fields : pairFieldsMatchB 188160 facet0 facet437 key0 key500 rowPose500 = true := by decide +kernel
theorem row500_generated : rootPair 500 = some rowPose500 :=
  pairFieldsMatchB_sound (by decide) row500_fields
theorem row500_source : sourceKey 500 ∈ geometry.profile (sourceOwner 500) := by decide +kernel
theorem row500_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 325 key8).FastValid geometry rowPose500 := by decide +kernel
theorem row500_illegal : ¬ geometry.LegalContact rowPose500 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row500_reject_checked)
theorem row500_classified : RowClassified 500 := by
  intro p generated legal
  have he : rowPose500 = p := Option.some.inj (row500_generated.symm.trans generated)
  subst p
  exact (row500_illegal legal).elim

def rowPose501 : Pose 7 := ⟨perm69, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row501_fields : pairFieldsMatchB 188160 facet0 facet438 key0 key501 rowPose501 = true := by decide +kernel
theorem row501_generated : rootPair 501 = some rowPose501 :=
  pairFieldsMatchB_sound (by decide) row501_fields
theorem row501_source : sourceKey 501 ∈ geometry.profile (sourceOwner 501) := by decide +kernel
theorem row501_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 438 key0).FastValid geometry rowPose501 := by decide +kernel
theorem row501_illegal : ¬ geometry.LegalContact rowPose501 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row501_reject_checked)
theorem row501_classified : RowClassified 501 := by
  intro p generated legal
  have he : rowPose501 = p := Option.some.inj (row501_generated.symm.trans generated)
  subst p
  exact (row501_illegal legal).elim

def rowPose502 : Pose 7 := ⟨perm90, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row502_fields : pairFieldsMatchB 188160 facet0 facet439 key0 key502 rowPose502 = true := by decide +kernel
theorem row502_generated : rootPair 502 = some rowPose502 :=
  pairFieldsMatchB_sound (by decide) row502_fields
theorem row502_source : sourceKey 502 ∈ geometry.profile (sourceOwner 502) := by decide +kernel
theorem row502_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 439 key0).FastValid geometry rowPose502 := by decide +kernel
theorem row502_illegal : ¬ geometry.LegalContact rowPose502 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row502_reject_checked)
theorem row502_classified : RowClassified 502 := by
  intro p generated legal
  have he : rowPose502 = p := Option.some.inj (row502_generated.symm.trans generated)
  subst p
  exact (row502_illegal legal).elim

def rowPose503 : Pose 7 := ⟨perm106, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row503_fields : pairFieldsMatchB 188160 facet0 facet440 key0 key503 rowPose503 = true := by decide +kernel
theorem row503_generated : rootPair 503 = some rowPose503 :=
  pairFieldsMatchB_sound (by decide) row503_fields
theorem row503_source : sourceKey 503 ∈ geometry.profile (sourceOwner 503) := by decide +kernel
theorem row503_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 440 key1).FastValid geometry rowPose503 := by decide +kernel
theorem row503_illegal : ¬ geometry.LegalContact rowPose503 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row503_reject_checked)
theorem row503_classified : RowClassified 503 := by
  intro p generated legal
  have he : rowPose503 = p := Option.some.inj (row503_generated.symm.trans generated)
  subst p
  exact (row503_illegal legal).elim

def rowPose504 : Pose 7 := ⟨perm0, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row504_fields : pairFieldsMatchB 188160 facet0 facet441 key0 key504 rowPose504 = true := by decide +kernel
theorem row504_generated : rootPair 504 = some rowPose504 :=
  pairFieldsMatchB_sound (by decide) row504_fields
theorem row504_source : sourceKey 504 ∈ geometry.profile (sourceOwner 504) := by decide +kernel
theorem row504_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 441 key0).FastValid geometry rowPose504 := by decide +kernel
theorem row504_illegal : ¬ geometry.LegalContact rowPose504 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row504_reject_checked)
theorem row504_classified : RowClassified 504 := by
  intro p generated legal
  have he : rowPose504 = p := Option.some.inj (row504_generated.symm.trans generated)
  subst p
  exact (row504_illegal legal).elim

def rowPose505 : Pose 7 := ⟨perm15, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row505_fields : pairFieldsMatchB 188160 facet0 facet441 key0 key505 rowPose505 = true := by decide +kernel
theorem row505_generated : rootPair 505 = some rowPose505 :=
  pairFieldsMatchB_sound (by decide) row505_fields
theorem row505_source : sourceKey 505 ∈ geometry.profile (sourceOwner 505) := by decide +kernel
theorem row505_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 217 key8).FastValid geometry rowPose505 := by decide +kernel
theorem row505_illegal : ¬ geometry.LegalContact rowPose505 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row505_reject_checked)
theorem row505_classified : RowClassified 505 := by
  intro p generated legal
  have he : rowPose505 = p := Option.some.inj (row505_generated.symm.trans generated)
  subst p
  exact (row505_illegal legal).elim

def rowPose506 : Pose 7 := ⟨perm0, ![false, false, false, false, false, false, false], ![-1, -1, -1, -1, -1, -1, -1]⟩
theorem row506_fields : pairFieldsMatchB 188160 facet0 facet442 key0 key506 rowPose506 = true := by decide +kernel
theorem row506_generated : rootPair 506 = some rowPose506 :=
  pairFieldsMatchB_sound (by decide) row506_fields
theorem row506_source : sourceKey 506 ∈ geometry.profile (sourceOwner 506) := by decide +kernel
theorem row506_catalog : rowPose506 ∈ M7 := by
  change rowPose506 ∈ Catalog7.supplied
  have he : rowPose506 = Catalog7.supplied.get ⟨238, by decide⟩ :=
    Pose.eq_of_sameCoordinates (by decide +kernel)
  rw [he]
  exact List.get_mem _ _
theorem row506_classified : RowClassified 506 := by
  intro p generated legal
  have he : rowPose506 = p := Option.some.inj (row506_generated.symm.trans generated)
  subst p
  exact row506_catalog

def rowPose507 : Pose 7 := ⟨perm15, ![false, false, false, false, false, false, false], ![-1, -1, -1, -1, -1, -1, -1]⟩
theorem row507_fields : pairFieldsMatchB 188160 facet0 facet442 key0 key507 rowPose507 = true := by decide +kernel
theorem row507_generated : rootPair 507 = some rowPose507 :=
  pairFieldsMatchB_sound (by decide) row507_fields
theorem row507_source : sourceKey 507 ∈ geometry.profile (sourceOwner 507) := by decide +kernel
theorem row507_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 442 key0).FastValid geometry rowPose507 := by decide +kernel
theorem row507_illegal : ¬ geometry.LegalContact rowPose507 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row507_reject_checked)
theorem row507_classified : RowClassified 507 := by
  intro p generated legal
  have he : rowPose507 = p := Option.some.inj (row507_generated.symm.trans generated)
  subst p
  exact (row507_illegal legal).elim

def rowPose508 : Pose 7 := ⟨perm21, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row508_fields : pairFieldsMatchB 188160 facet0 facet443 key0 key508 rowPose508 = true := by decide +kernel
theorem row508_generated : rootPair 508 = some rowPose508 :=
  pairFieldsMatchB_sound (by decide) row508_fields
theorem row508_source : sourceKey 508 ∈ geometry.profile (sourceOwner 508) := by decide +kernel
theorem row508_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 443 key1).FastValid geometry rowPose508 := by decide +kernel
theorem row508_illegal : ¬ geometry.LegalContact rowPose508 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row508_reject_checked)
theorem row508_classified : RowClassified 508 := by
  intro p generated legal
  have he : rowPose508 = p := Option.some.inj (row508_generated.symm.trans generated)
  subst p
  exact (row508_illegal legal).elim

def rowPose509 : Pose 7 := ⟨perm42, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row509_fields : pairFieldsMatchB 188160 facet0 facet444 key0 key509 rowPose509 = true := by decide +kernel
theorem row509_generated : rootPair 509 = some rowPose509 :=
  pairFieldsMatchB_sound (by decide) row509_fields
theorem row509_source : sourceKey 509 ∈ geometry.profile (sourceOwner 509) := by decide +kernel
theorem row509_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 444 key1).FastValid geometry rowPose509 := by decide +kernel
theorem row509_illegal : ¬ geometry.LegalContact rowPose509 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row509_reject_checked)
theorem row509_classified : RowClassified 509 := by
  intro p generated legal
  have he : rowPose509 = p := Option.some.inj (row509_generated.symm.trans generated)
  subst p
  exact (row509_illegal legal).elim

def rowPose510 : Pose 7 := ⟨perm55, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row510_fields : pairFieldsMatchB 188160 facet0 facet445 key0 key510 rowPose510 = true := by decide +kernel
theorem row510_generated : rootPair 510 = some rowPose510 :=
  pairFieldsMatchB_sound (by decide) row510_fields
theorem row510_source : sourceKey 510 ∈ geometry.profile (sourceOwner 510) := by decide +kernel
theorem row510_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 445 key0).FastValid geometry rowPose510 := by decide +kernel
theorem row510_illegal : ¬ geometry.LegalContact rowPose510 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row510_reject_checked)
theorem row510_classified : RowClassified 510 := by
  intro p generated legal
  have he : rowPose510 = p := Option.some.inj (row510_generated.symm.trans generated)
  subst p
  exact (row510_illegal legal).elim

def rowPose511 : Pose 7 := ⟨perm73, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, -1, 0, 2]⟩
theorem row511_fields : pairFieldsMatchB 188160 facet0 facet446 key0 key511 rowPose511 = true := by decide +kernel
theorem row511_generated : rootPair 511 = some rowPose511 :=
  pairFieldsMatchB_sound (by decide) row511_fields
theorem row511_source : sourceKey 511 ∈ geometry.profile (sourceOwner 511) := by decide +kernel
theorem row511_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 446 key1).FastValid geometry rowPose511 := by decide +kernel
theorem row511_illegal : ¬ geometry.LegalContact rowPose511 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row511_reject_checked)
theorem row511_classified : RowClassified 511 := by
  intro p generated legal
  have he : rowPose511 = p := Option.some.inj (row511_generated.symm.trans generated)
  subst p
  exact (row511_illegal legal).elim

theorem chunk15_classified (i : Fin 32) : RowClassified ⟨480 + i.val, by omega⟩ := by
  fin_cases i
  · exact row480_classified
  · exact row481_classified
  · exact row482_classified
  · exact row483_classified
  · exact row484_classified
  · exact row485_classified
  · exact row486_classified
  · exact row487_classified
  · exact row488_classified
  · exact row489_classified
  · exact row490_classified
  · exact row491_classified
  · exact row492_classified
  · exact row493_classified
  · exact row494_classified
  · exact row495_classified
  · exact row496_classified
  · exact row497_classified
  · exact row498_classified
  · exact row499_classified
  · exact row500_classified
  · exact row501_classified
  · exact row502_classified
  · exact row503_classified
  · exact row504_classified
  · exact row505_classified
  · exact row506_classified
  · exact row507_classified
  · exact row508_classified
  · exact row509_classified
  · exact row510_classified
  · exact row511_classified

theorem chunk15_source (i : Fin 32) : sourceKey ⟨480 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨480 + i.val, by omega⟩) := by
  fin_cases i
  · exact row480_source
  · exact row481_source
  · exact row482_source
  · exact row483_source
  · exact row484_source
  · exact row485_source
  · exact row486_source
  · exact row487_source
  · exact row488_source
  · exact row489_source
  · exact row490_source
  · exact row491_source
  · exact row492_source
  · exact row493_source
  · exact row494_source
  · exact row495_source
  · exact row496_source
  · exact row497_source
  · exact row498_source
  · exact row499_source
  · exact row500_source
  · exact row501_source
  · exact row502_source
  · exact row503_source
  · exact row504_source
  · exact row505_source
  · exact row506_source
  · exact row507_source
  · exact row508_source
  · exact row509_source
  · exact row510_source
  · exact row511_source

#print axioms chunk15_classified
end SparseMonotiles.Contact.RootZeroPilot7
