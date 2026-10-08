module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose512 : Pose 7 := ⟨perm87, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row512_fields : pairFieldsMatchB 188160 facet0 facet447 key0 key512 rowPose512 = true := by decide +kernel
theorem row512_generated : rootPair 512 = some rowPose512 :=
  pairFieldsMatchB_sound (by decide) row512_fields
theorem row512_source : sourceKey 512 ∈ geometry.profile (sourceOwner 512) := by decide +kernel
theorem row512_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 447 key0).FastValid geometry rowPose512 := by decide +kernel
theorem row512_illegal : ¬ geometry.LegalContact rowPose512 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row512_reject_checked)
theorem row512_classified : RowClassified 512 := by
  intro p generated legal
  have he : rowPose512 = p := Option.some.inj (row512_generated.symm.trans generated)
  subst p
  exact (row512_illegal legal).elim

def rowPose513 : Pose 7 := ⟨perm96, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row513_fields : pairFieldsMatchB 188160 facet0 facet448 key0 key513 rowPose513 = true := by decide +kernel
theorem row513_generated : rootPair 513 = some rowPose513 :=
  pairFieldsMatchB_sound (by decide) row513_fields
theorem row513_source : sourceKey 513 ∈ geometry.profile (sourceOwner 513) := by decide +kernel
theorem row513_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 448 key0).FastValid geometry rowPose513 := by decide +kernel
theorem row513_illegal : ¬ geometry.LegalContact rowPose513 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row513_reject_checked)
theorem row513_classified : RowClassified 513 := by
  intro p generated legal
  have he : rowPose513 = p := Option.some.inj (row513_generated.symm.trans generated)
  subst p
  exact (row513_illegal legal).elim

def rowPose514 : Pose 7 := ⟨perm0, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row514_fields : pairFieldsMatchB 188160 facet0 facet449 key0 key514 rowPose514 = true := by decide +kernel
theorem row514_generated : rootPair 514 = some rowPose514 :=
  pairFieldsMatchB_sound (by decide) row514_fields
theorem row514_source : sourceKey 514 ∈ geometry.profile (sourceOwner 514) := by decide +kernel
theorem row514_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 456 key8).FastValid geometry rowPose514 := by decide +kernel
theorem row514_illegal : ¬ geometry.LegalContact rowPose514 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row514_reject_checked)
theorem row514_classified : RowClassified 514 := by
  intro p generated legal
  have he : rowPose514 = p := Option.some.inj (row514_generated.symm.trans generated)
  subst p
  exact (row514_illegal legal).elim

def rowPose515 : Pose 7 := ⟨perm15, ![false, false, false, false, false, false, false], ![-2, 0, 0, 0, 0, 0, 0]⟩
theorem row515_fields : pairFieldsMatchB 188160 facet0 facet449 key0 key515 rowPose515 = true := by decide +kernel
theorem row515_generated : rootPair 515 = some rowPose515 :=
  pairFieldsMatchB_sound (by decide) row515_fields
theorem row515_source : sourceKey 515 ∈ geometry.profile (sourceOwner 515) := by decide +kernel
theorem row515_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 449 key0).FastValid geometry rowPose515 := by decide +kernel
theorem row515_illegal : ¬ geometry.LegalContact rowPose515 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row515_reject_checked)
theorem row515_classified : RowClassified 515 := by
  intro p generated legal
  have he : rowPose515 = p := Option.some.inj (row515_generated.symm.trans generated)
  subst p
  exact (row515_illegal legal).elim

def rowPose516 : Pose 7 := ⟨perm21, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row516_fields : pairFieldsMatchB 188160 facet0 facet450 key0 key516 rowPose516 = true := by decide +kernel
theorem row516_generated : rootPair 516 = some rowPose516 :=
  pairFieldsMatchB_sound (by decide) row516_fields
theorem row516_source : sourceKey 516 ∈ geometry.profile (sourceOwner 516) := by decide +kernel
theorem row516_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 450 key0).FastValid geometry rowPose516 := by decide +kernel
theorem row516_illegal : ¬ geometry.LegalContact rowPose516 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row516_reject_checked)
theorem row516_classified : RowClassified 516 := by
  intro p generated legal
  have he : rowPose516 = p := Option.some.inj (row516_generated.symm.trans generated)
  subst p
  exact (row516_illegal legal).elim

def rowPose517 : Pose 7 := ⟨perm42, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row517_fields : pairFieldsMatchB 188160 facet0 facet451 key0 key517 rowPose517 = true := by decide +kernel
theorem row517_generated : rootPair 517 = some rowPose517 :=
  pairFieldsMatchB_sound (by decide) row517_fields
theorem row517_source : sourceKey 517 ∈ geometry.profile (sourceOwner 517) := by decide +kernel
theorem row517_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 451 key0).FastValid geometry rowPose517 := by decide +kernel
theorem row517_illegal : ¬ geometry.LegalContact rowPose517 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row517_reject_checked)
theorem row517_classified : RowClassified 517 := by
  intro p generated legal
  have he : rowPose517 = p := Option.some.inj (row517_generated.symm.trans generated)
  subst p
  exact (row517_illegal legal).elim

def rowPose518 : Pose 7 := ⟨perm55, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row518_fields : pairFieldsMatchB 188160 facet0 facet452 key0 key518 rowPose518 = true := by decide +kernel
theorem row518_generated : rootPair 518 = some rowPose518 :=
  pairFieldsMatchB_sound (by decide) row518_fields
theorem row518_source : sourceKey 518 ∈ geometry.profile (sourceOwner 518) := by decide +kernel
theorem row518_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 452 key1).FastValid geometry rowPose518 := by decide +kernel
theorem row518_illegal : ¬ geometry.LegalContact rowPose518 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row518_reject_checked)
theorem row518_classified : RowClassified 518 := by
  intro p generated legal
  have he : rowPose518 = p := Option.some.inj (row518_generated.symm.trans generated)
  subst p
  exact (row518_illegal legal).elim

def rowPose519 : Pose 7 := ⟨perm73, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 1, 2, 0]⟩
theorem row519_fields : pairFieldsMatchB 188160 facet0 facet453 key0 key519 rowPose519 = true := by decide +kernel
theorem row519_generated : rootPair 519 = some rowPose519 :=
  pairFieldsMatchB_sound (by decide) row519_fields
theorem row519_source : sourceKey 519 ∈ geometry.profile (sourceOwner 519) := by decide +kernel
theorem row519_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 453 key0).FastValid geometry rowPose519 := by decide +kernel
theorem row519_illegal : ¬ geometry.LegalContact rowPose519 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row519_reject_checked)
theorem row519_classified : RowClassified 519 := by
  intro p generated legal
  have he : rowPose519 = p := Option.some.inj (row519_generated.symm.trans generated)
  subst p
  exact (row519_illegal legal).elim

def rowPose520 : Pose 7 := ⟨perm87, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, 0, -1, 1]⟩
theorem row520_fields : pairFieldsMatchB 188160 facet0 facet454 key0 key520 rowPose520 = true := by decide +kernel
theorem row520_generated : rootPair 520 = some rowPose520 :=
  pairFieldsMatchB_sound (by decide) row520_fields
theorem row520_source : sourceKey 520 ∈ geometry.profile (sourceOwner 520) := by decide +kernel
theorem row520_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 454 key1).FastValid geometry rowPose520 := by decide +kernel
theorem row520_illegal : ¬ geometry.LegalContact rowPose520 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row520_reject_checked)
theorem row520_classified : RowClassified 520 := by
  intro p generated legal
  have he : rowPose520 = p := Option.some.inj (row520_generated.symm.trans generated)
  subst p
  exact (row520_illegal legal).elim

def rowPose521 : Pose 7 := ⟨perm96, ![true, false, false, false, true, true, true], ![0, -1, 0, 0, 1, 1, 1]⟩
theorem row521_fields : pairFieldsMatchB 188160 facet0 facet455 key0 key521 rowPose521 = true := by decide +kernel
theorem row521_generated : rootPair 521 = some rowPose521 :=
  pairFieldsMatchB_sound (by decide) row521_fields
theorem row521_source : sourceKey 521 ∈ geometry.profile (sourceOwner 521) := by decide +kernel
theorem row521_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 455 key1).FastValid geometry rowPose521 := by decide +kernel
theorem row521_illegal : ¬ geometry.LegalContact rowPose521 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row521_reject_checked)
theorem row521_classified : RowClassified 521 := by
  intro p generated legal
  have he : rowPose521 = p := Option.some.inj (row521_generated.symm.trans generated)
  subst p
  exact (row521_illegal legal).elim

def rowPose522 : Pose 7 := ⟨perm5, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row522_fields : pairFieldsMatchB 188160 facet0 facet456 key0 key522 rowPose522 = true := by decide +kernel
theorem row522_generated : rootPair 522 = some rowPose522 :=
  pairFieldsMatchB_sound (by decide) row522_fields
theorem row522_source : sourceKey 522 ∈ geometry.profile (sourceOwner 522) := by decide +kernel
theorem row522_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 456 key1).FastValid geometry rowPose522 := by decide +kernel
theorem row522_illegal : ¬ geometry.LegalContact rowPose522 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row522_reject_checked)
theorem row522_classified : RowClassified 522 := by
  intro p generated legal
  have he : rowPose522 = p := Option.some.inj (row522_generated.symm.trans generated)
  subst p
  exact (row522_illegal legal).elim

def rowPose523 : Pose 7 := ⟨perm21, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row523_fields : pairFieldsMatchB 188160 facet0 facet457 key0 key523 rowPose523 = true := by decide +kernel
theorem row523_generated : rootPair 523 = some rowPose523 :=
  pairFieldsMatchB_sound (by decide) row523_fields
theorem row523_source : sourceKey 523 ∈ geometry.profile (sourceOwner 523) := by decide +kernel
theorem row523_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 457 key0).FastValid geometry rowPose523 := by decide +kernel
theorem row523_illegal : ¬ geometry.LegalContact rowPose523 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row523_reject_checked)
theorem row523_classified : RowClassified 523 := by
  intro p generated legal
  have he : rowPose523 = p := Option.some.inj (row523_generated.symm.trans generated)
  subst p
  exact (row523_illegal legal).elim

def rowPose524 : Pose 7 := ⟨perm42, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row524_fields : pairFieldsMatchB 188160 facet0 facet458 key0 key524 rowPose524 = true := by decide +kernel
theorem row524_generated : rootPair 524 = some rowPose524 :=
  pairFieldsMatchB_sound (by decide) row524_fields
theorem row524_source : sourceKey 524 ∈ geometry.profile (sourceOwner 524) := by decide +kernel
theorem row524_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 458 key0).FastValid geometry rowPose524 := by decide +kernel
theorem row524_illegal : ¬ geometry.LegalContact rowPose524 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row524_reject_checked)
theorem row524_classified : RowClassified 524 := by
  intro p generated legal
  have he : rowPose524 = p := Option.some.inj (row524_generated.symm.trans generated)
  subst p
  exact (row524_illegal legal).elim

def rowPose525 : Pose 7 := ⟨perm53, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row525_fields : pairFieldsMatchB 188160 facet0 facet459 key0 key525 rowPose525 = true := by decide +kernel
theorem row525_generated : rootPair 525 = some rowPose525 :=
  pairFieldsMatchB_sound (by decide) row525_fields
theorem row525_source : sourceKey 525 ∈ geometry.profile (sourceOwner 525) := by decide +kernel
theorem row525_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 487 key8).FastValid geometry rowPose525 := by decide +kernel
theorem row525_illegal : ¬ geometry.LegalContact rowPose525 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row525_reject_checked)
theorem row525_classified : RowClassified 525 := by
  intro p generated legal
  have he : rowPose525 = p := Option.some.inj (row525_generated.symm.trans generated)
  subst p
  exact (row525_illegal legal).elim

def rowPose526 : Pose 7 := ⟨perm58, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row526_fields : pairFieldsMatchB 188160 facet0 facet459 key0 key526 rowPose526 = true := by decide +kernel
theorem row526_generated : rootPair 526 = some rowPose526 :=
  pairFieldsMatchB_sound (by decide) row526_fields
theorem row526_source : sourceKey 526 ∈ geometry.profile (sourceOwner 526) := by decide +kernel
theorem row526_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 459 key0).FastValid geometry rowPose526 := by decide +kernel
theorem row526_illegal : ¬ geometry.LegalContact rowPose526 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row526_reject_checked)
theorem row526_classified : RowClassified 526 := by
  intro p generated legal
  have he : rowPose526 = p := Option.some.inj (row526_generated.symm.trans generated)
  subst p
  exact (row526_illegal legal).elim

def rowPose527 : Pose 7 := ⟨perm69, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row527_fields : pairFieldsMatchB 188160 facet0 facet460 key0 key527 rowPose527 = true := by decide +kernel
theorem row527_generated : rootPair 527 = some rowPose527 :=
  pairFieldsMatchB_sound (by decide) row527_fields
theorem row527_source : sourceKey 527 ∈ geometry.profile (sourceOwner 527) := by decide +kernel
theorem row527_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 460 key1).FastValid geometry rowPose527 := by decide +kernel
theorem row527_illegal : ¬ geometry.LegalContact rowPose527 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row527_reject_checked)
theorem row527_classified : RowClassified 527 := by
  intro p generated legal
  have he : rowPose527 = p := Option.some.inj (row527_generated.symm.trans generated)
  subst p
  exact (row527_illegal legal).elim

def rowPose528 : Pose 7 := ⟨perm90, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row528_fields : pairFieldsMatchB 188160 facet0 facet461 key0 key528 rowPose528 = true := by decide +kernel
theorem row528_generated : rootPair 528 = some rowPose528 :=
  pairFieldsMatchB_sound (by decide) row528_fields
theorem row528_source : sourceKey 528 ∈ geometry.profile (sourceOwner 528) := by decide +kernel
theorem row528_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 461 key1).FastValid geometry rowPose528 := by decide +kernel
theorem row528_illegal : ¬ geometry.LegalContact rowPose528 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row528_reject_checked)
theorem row528_classified : RowClassified 528 := by
  intro p generated legal
  have he : rowPose528 = p := Option.some.inj (row528_generated.symm.trans generated)
  subst p
  exact (row528_illegal legal).elim

def rowPose529 : Pose 7 := ⟨perm106, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row529_fields : pairFieldsMatchB 188160 facet0 facet462 key0 key529 rowPose529 = true := by decide +kernel
theorem row529_generated : rootPair 529 = some rowPose529 :=
  pairFieldsMatchB_sound (by decide) row529_fields
theorem row529_source : sourceKey 529 ∈ geometry.profile (sourceOwner 529) := by decide +kernel
theorem row529_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 462 key0).FastValid geometry rowPose529 := by decide +kernel
theorem row529_illegal : ¬ geometry.LegalContact rowPose529 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row529_reject_checked)
theorem row529_classified : RowClassified 529 := by
  intro p generated legal
  have he : rowPose529 = p := Option.some.inj (row529_generated.symm.trans generated)
  subst p
  exact (row529_illegal legal).elim

def rowPose530 : Pose 7 := ⟨perm15, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row530_fields : pairFieldsMatchB 188160 facet0 facet463 key0 key530 rowPose530 = true := by decide +kernel
theorem row530_generated : rootPair 530 = some rowPose530 :=
  pairFieldsMatchB_sound (by decide) row530_fields
theorem row530_source : sourceKey 530 ∈ geometry.profile (sourceOwner 530) := by decide +kernel
theorem row530_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 463 key1).FastValid geometry rowPose530 := by decide +kernel
theorem row530_illegal : ¬ geometry.LegalContact rowPose530 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row530_reject_checked)
theorem row530_classified : RowClassified 530 := by
  intro p generated legal
  have he : rowPose530 = p := Option.some.inj (row530_generated.symm.trans generated)
  subst p
  exact (row530_illegal legal).elim

def rowPose531 : Pose 7 := ⟨perm24, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row531_fields : pairFieldsMatchB 188160 facet0 facet464 key0 key531 rowPose531 = true := by decide +kernel
theorem row531_generated : rootPair 531 = some rowPose531 :=
  pairFieldsMatchB_sound (by decide) row531_fields
theorem row531_source : sourceKey 531 ∈ geometry.profile (sourceOwner 531) := by decide +kernel
theorem row531_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 464 key1).FastValid geometry rowPose531 := by decide +kernel
theorem row531_illegal : ¬ geometry.LegalContact rowPose531 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row531_reject_checked)
theorem row531_classified : RowClassified 531 := by
  intro p generated legal
  have he : rowPose531 = p := Option.some.inj (row531_generated.symm.trans generated)
  subst p
  exact (row531_illegal legal).elim

def rowPose532 : Pose 7 := ⟨perm38, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row532_fields : pairFieldsMatchB 188160 facet0 facet465 key0 key532 rowPose532 = true := by decide +kernel
theorem row532_generated : rootPair 532 = some rowPose532 :=
  pairFieldsMatchB_sound (by decide) row532_fields
theorem row532_source : sourceKey 532 ∈ geometry.profile (sourceOwner 532) := by decide +kernel
theorem row532_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 465 key0).FastValid geometry rowPose532 := by decide +kernel
theorem row532_illegal : ¬ geometry.LegalContact rowPose532 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row532_reject_checked)
theorem row532_classified : RowClassified 532 := by
  intro p generated legal
  have he : rowPose532 = p := Option.some.inj (row532_generated.symm.trans generated)
  subst p
  exact (row532_illegal legal).elim

def rowPose533 : Pose 7 := ⟨perm56, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row533_fields : pairFieldsMatchB 188160 facet0 facet466 key0 key533 rowPose533 = true := by decide +kernel
theorem row533_generated : rootPair 533 = some rowPose533 :=
  pairFieldsMatchB_sound (by decide) row533_fields
theorem row533_source : sourceKey 533 ∈ geometry.profile (sourceOwner 533) := by decide +kernel
theorem row533_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 466 key1).FastValid geometry rowPose533 := by decide +kernel
theorem row533_illegal : ¬ geometry.LegalContact rowPose533 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row533_reject_checked)
theorem row533_classified : RowClassified 533 := by
  intro p generated legal
  have he : rowPose533 = p := Option.some.inj (row533_generated.symm.trans generated)
  subst p
  exact (row533_illegal legal).elim

def rowPose534 : Pose 7 := ⟨perm69, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row534_fields : pairFieldsMatchB 188160 facet0 facet467 key0 key534 rowPose534 = true := by decide +kernel
theorem row534_generated : rootPair 534 = some rowPose534 :=
  pairFieldsMatchB_sound (by decide) row534_fields
theorem row534_source : sourceKey 534 ∈ geometry.profile (sourceOwner 534) := by decide +kernel
theorem row534_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 467 key0).FastValid geometry rowPose534 := by decide +kernel
theorem row534_illegal : ¬ geometry.LegalContact rowPose534 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row534_reject_checked)
theorem row534_classified : RowClassified 534 := by
  intro p generated legal
  have he : rowPose534 = p := Option.some.inj (row534_generated.symm.trans generated)
  subst p
  exact (row534_illegal legal).elim

def rowPose535 : Pose 7 := ⟨perm90, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row535_fields : pairFieldsMatchB 188160 facet0 facet468 key0 key535 rowPose535 = true := by decide +kernel
theorem row535_generated : rootPair 535 = some rowPose535 :=
  pairFieldsMatchB_sound (by decide) row535_fields
theorem row535_source : sourceKey 535 ∈ geometry.profile (sourceOwner 535) := by decide +kernel
theorem row535_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 468 key0).FastValid geometry rowPose535 := by decide +kernel
theorem row535_illegal : ¬ geometry.LegalContact rowPose535 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row535_reject_checked)
theorem row535_classified : RowClassified 535 := by
  intro p generated legal
  have he : rowPose535 = p := Option.some.inj (row535_generated.symm.trans generated)
  subst p
  exact (row535_illegal legal).elim

def rowPose536 : Pose 7 := ⟨perm96, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row536_fields : pairFieldsMatchB 188160 facet0 facet469 key0 key536 rowPose536 = true := by decide +kernel
theorem row536_generated : rootPair 536 = some rowPose536 :=
  pairFieldsMatchB_sound (by decide) row536_fields
theorem row536_source : sourceKey 536 ∈ geometry.profile (sourceOwner 536) := by decide +kernel
theorem row536_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 469 key0).FastValid geometry rowPose536 := by decide +kernel
theorem row536_illegal : ¬ geometry.LegalContact rowPose536 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row536_reject_checked)
theorem row536_classified : RowClassified 536 := by
  intro p generated legal
  have he : rowPose536 = p := Option.some.inj (row536_generated.symm.trans generated)
  subst p
  exact (row536_illegal legal).elim

def rowPose537 : Pose 7 := ⟨perm111, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row537_fields : pairFieldsMatchB 188160 facet0 facet469 key0 key537 rowPose537 = true := by decide +kernel
theorem row537_generated : rootPair 537 = some rowPose537 :=
  pairFieldsMatchB_sound (by decide) row537_fields
theorem row537_source : sourceKey 537 ∈ geometry.profile (sourceOwner 537) := by decide +kernel
theorem row537_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 20 key8).FastValid geometry rowPose537 := by decide +kernel
theorem row537_illegal : ¬ geometry.LegalContact rowPose537 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row537_reject_checked)
theorem row537_classified : RowClassified 537 := by
  intro p generated legal
  have he : rowPose537 = p := Option.some.inj (row537_generated.symm.trans generated)
  subst p
  exact (row537_illegal legal).elim

def rowPose538 : Pose 7 := ⟨perm15, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row538_fields : pairFieldsMatchB 188160 facet0 facet470 key0 key538 rowPose538 = true := by decide +kernel
theorem row538_generated : rootPair 538 = some rowPose538 :=
  pairFieldsMatchB_sound (by decide) row538_fields
theorem row538_source : sourceKey 538 ∈ geometry.profile (sourceOwner 538) := by decide +kernel
theorem row538_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 470 key0).FastValid geometry rowPose538 := by decide +kernel
theorem row538_illegal : ¬ geometry.LegalContact rowPose538 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row538_reject_checked)
theorem row538_classified : RowClassified 538 := by
  intro p generated legal
  have he : rowPose538 = p := Option.some.inj (row538_generated.symm.trans generated)
  subst p
  exact (row538_illegal legal).elim

def rowPose539 : Pose 7 := ⟨perm24, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row539_fields : pairFieldsMatchB 188160 facet0 facet471 key0 key539 rowPose539 = true := by decide +kernel
theorem row539_generated : rootPair 539 = some rowPose539 :=
  pairFieldsMatchB_sound (by decide) row539_fields
theorem row539_source : sourceKey 539 ∈ geometry.profile (sourceOwner 539) := by decide +kernel
theorem row539_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 471 key0).FastValid geometry rowPose539 := by decide +kernel
theorem row539_illegal : ¬ geometry.LegalContact rowPose539 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row539_reject_checked)
theorem row539_classified : RowClassified 539 := by
  intro p generated legal
  have he : rowPose539 = p := Option.some.inj (row539_generated.symm.trans generated)
  subst p
  exact (row539_illegal legal).elim

def rowPose540 : Pose 7 := ⟨perm38, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row540_fields : pairFieldsMatchB 188160 facet0 facet472 key0 key540 rowPose540 = true := by decide +kernel
theorem row540_generated : rootPair 540 = some rowPose540 :=
  pairFieldsMatchB_sound (by decide) row540_fields
theorem row540_source : sourceKey 540 ∈ geometry.profile (sourceOwner 540) := by decide +kernel
theorem row540_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 472 key1).FastValid geometry rowPose540 := by decide +kernel
theorem row540_illegal : ¬ geometry.LegalContact rowPose540 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row540_reject_checked)
theorem row540_classified : RowClassified 540 := by
  intro p generated legal
  have he : rowPose540 = p := Option.some.inj (row540_generated.symm.trans generated)
  subst p
  exact (row540_illegal legal).elim

def rowPose541 : Pose 7 := ⟨perm56, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row541_fields : pairFieldsMatchB 188160 facet0 facet473 key0 key541 rowPose541 = true := by decide +kernel
theorem row541_generated : rootPair 541 = some rowPose541 :=
  pairFieldsMatchB_sound (by decide) row541_fields
theorem row541_source : sourceKey 541 ∈ geometry.profile (sourceOwner 541) := by decide +kernel
theorem row541_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 473 key0).FastValid geometry rowPose541 := by decide +kernel
theorem row541_illegal : ¬ geometry.LegalContact rowPose541 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row541_reject_checked)
theorem row541_classified : RowClassified 541 := by
  intro p generated legal
  have he : rowPose541 = p := Option.some.inj (row541_generated.symm.trans generated)
  subst p
  exact (row541_illegal legal).elim

def rowPose542 : Pose 7 := ⟨perm69, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row542_fields : pairFieldsMatchB 188160 facet0 facet474 key0 key542 rowPose542 = true := by decide +kernel
theorem row542_generated : rootPair 542 = some rowPose542 :=
  pairFieldsMatchB_sound (by decide) row542_fields
theorem row542_source : sourceKey 542 ∈ geometry.profile (sourceOwner 542) := by decide +kernel
theorem row542_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 474 key1).FastValid geometry rowPose542 := by decide +kernel
theorem row542_illegal : ¬ geometry.LegalContact rowPose542 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row542_reject_checked)
theorem row542_classified : RowClassified 542 := by
  intro p generated legal
  have he : rowPose542 = p := Option.some.inj (row542_generated.symm.trans generated)
  subst p
  exact (row542_illegal legal).elim

def rowPose543 : Pose 7 := ⟨perm90, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row543_fields : pairFieldsMatchB 188160 facet0 facet475 key0 key543 rowPose543 = true := by decide +kernel
theorem row543_generated : rootPair 543 = some rowPose543 :=
  pairFieldsMatchB_sound (by decide) row543_fields
theorem row543_source : sourceKey 543 ∈ geometry.profile (sourceOwner 543) := by decide +kernel
theorem row543_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 475 key1).FastValid geometry rowPose543 := by decide +kernel
theorem row543_illegal : ¬ geometry.LegalContact rowPose543 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row543_reject_checked)
theorem row543_classified : RowClassified 543 := by
  intro p generated legal
  have he : rowPose543 = p := Option.some.inj (row543_generated.symm.trans generated)
  subst p
  exact (row543_illegal legal).elim

theorem chunk16_classified (i : Fin 32) : RowClassified ⟨512 + i.val, by omega⟩ := by
  fin_cases i
  · exact row512_classified
  · exact row513_classified
  · exact row514_classified
  · exact row515_classified
  · exact row516_classified
  · exact row517_classified
  · exact row518_classified
  · exact row519_classified
  · exact row520_classified
  · exact row521_classified
  · exact row522_classified
  · exact row523_classified
  · exact row524_classified
  · exact row525_classified
  · exact row526_classified
  · exact row527_classified
  · exact row528_classified
  · exact row529_classified
  · exact row530_classified
  · exact row531_classified
  · exact row532_classified
  · exact row533_classified
  · exact row534_classified
  · exact row535_classified
  · exact row536_classified
  · exact row537_classified
  · exact row538_classified
  · exact row539_classified
  · exact row540_classified
  · exact row541_classified
  · exact row542_classified
  · exact row543_classified

theorem chunk16_source (i : Fin 32) : sourceKey ⟨512 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨512 + i.val, by omega⟩) := by
  fin_cases i
  · exact row512_source
  · exact row513_source
  · exact row514_source
  · exact row515_source
  · exact row516_source
  · exact row517_source
  · exact row518_source
  · exact row519_source
  · exact row520_source
  · exact row521_source
  · exact row522_source
  · exact row523_source
  · exact row524_source
  · exact row525_source
  · exact row526_source
  · exact row527_source
  · exact row528_source
  · exact row529_source
  · exact row530_source
  · exact row531_source
  · exact row532_source
  · exact row533_source
  · exact row534_source
  · exact row535_source
  · exact row536_source
  · exact row537_source
  · exact row538_source
  · exact row539_source
  · exact row540_source
  · exact row541_source
  · exact row542_source
  · exact row543_source

#print axioms chunk16_classified
end SparseMonotiles.Contact.RootZeroPilot7
