module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose544 : Pose 7 := ⟨perm96, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row544_fields : pairFieldsMatchB 188160 facet0 facet476 key0 key544 rowPose544 = true := by decide +kernel
theorem row544_generated : rootPair 544 = some rowPose544 :=
  pairFieldsMatchB_sound (by decide) row544_fields
theorem row544_source : sourceKey 544 ∈ geometry.profile (sourceOwner 544) := by decide +kernel
theorem row544_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 462 key8).FastValid geometry rowPose544 := by decide +kernel
theorem row544_illegal : ¬ geometry.LegalContact rowPose544 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row544_reject_checked)
theorem row544_classified : RowClassified 544 := by
  intro p generated legal
  have he : rowPose544 = p := Option.some.inj (row544_generated.symm.trans generated)
  subst p
  exact (row544_illegal legal).elim

def rowPose545 : Pose 7 := ⟨perm111, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row545_fields : pairFieldsMatchB 188160 facet0 facet476 key0 key545 rowPose545 = true := by decide +kernel
theorem row545_generated : rootPair 545 = some rowPose545 :=
  pairFieldsMatchB_sound (by decide) row545_fields
theorem row545_source : sourceKey 545 ∈ geometry.profile (sourceOwner 545) := by decide +kernel
theorem row545_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 476 key0).FastValid geometry rowPose545 := by decide +kernel
theorem row545_illegal : ¬ geometry.LegalContact rowPose545 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row545_reject_checked)
theorem row545_classified : RowClassified 545 := by
  intro p generated legal
  have he : rowPose545 = p := Option.some.inj (row545_generated.symm.trans generated)
  subst p
  exact (row545_illegal legal).elim

def rowPose546 : Pose 7 := ⟨perm15, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row546_fields : pairFieldsMatchB 188160 facet0 facet477 key0 key546 rowPose546 = true := by decide +kernel
theorem row546_generated : rootPair 546 = some rowPose546 :=
  pairFieldsMatchB_sound (by decide) row546_fields
theorem row546_source : sourceKey 546 ∈ geometry.profile (sourceOwner 546) := by decide +kernel
theorem row546_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 477 key0).FastValid geometry rowPose546 := by decide +kernel
theorem row546_illegal : ¬ geometry.LegalContact rowPose546 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row546_reject_checked)
theorem row546_classified : RowClassified 546 := by
  intro p generated legal
  have he : rowPose546 = p := Option.some.inj (row546_generated.symm.trans generated)
  subst p
  exact (row546_illegal legal).elim

def rowPose547 : Pose 7 := ⟨perm24, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row547_fields : pairFieldsMatchB 188160 facet0 facet478 key0 key547 rowPose547 = true := by decide +kernel
theorem row547_generated : rootPair 547 = some rowPose547 :=
  pairFieldsMatchB_sound (by decide) row547_fields
theorem row547_source : sourceKey 547 ∈ geometry.profile (sourceOwner 547) := by decide +kernel
theorem row547_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 478 key0).FastValid geometry rowPose547 := by decide +kernel
theorem row547_illegal : ¬ geometry.LegalContact rowPose547 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row547_reject_checked)
theorem row547_classified : RowClassified 547 := by
  intro p generated legal
  have he : rowPose547 = p := Option.some.inj (row547_generated.symm.trans generated)
  subst p
  exact (row547_illegal legal).elim

def rowPose548 : Pose 7 := ⟨perm37, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row548_fields : pairFieldsMatchB 188160 facet0 facet479 key0 key548 rowPose548 = true := by decide +kernel
theorem row548_generated : rootPair 548 = some rowPose548 :=
  pairFieldsMatchB_sound (by decide) row548_fields
theorem row548_source : sourceKey 548 ∈ geometry.profile (sourceOwner 548) := by decide +kernel
theorem row548_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 535 key8).FastValid geometry rowPose548 := by decide +kernel
theorem row548_illegal : ¬ geometry.LegalContact rowPose548 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row548_reject_checked)
theorem row548_classified : RowClassified 548 := by
  intro p generated legal
  have he : rowPose548 = p := Option.some.inj (row548_generated.symm.trans generated)
  subst p
  exact (row548_illegal legal).elim

def rowPose549 : Pose 7 := ⟨perm42, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row549_fields : pairFieldsMatchB 188160 facet0 facet479 key0 key549 rowPose549 = true := by decide +kernel
theorem row549_generated : rootPair 549 = some rowPose549 :=
  pairFieldsMatchB_sound (by decide) row549_fields
theorem row549_source : sourceKey 549 ∈ geometry.profile (sourceOwner 549) := by decide +kernel
theorem row549_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 479 key0).FastValid geometry rowPose549 := by decide +kernel
theorem row549_illegal : ¬ geometry.LegalContact rowPose549 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row549_reject_checked)
theorem row549_classified : RowClassified 549 := by
  intro p generated legal
  have he : rowPose549 = p := Option.some.inj (row549_generated.symm.trans generated)
  subst p
  exact (row549_illegal legal).elim

def rowPose550 : Pose 7 := ⟨perm53, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row550_fields : pairFieldsMatchB 188160 facet0 facet480 key0 key550 rowPose550 = true := by decide +kernel
theorem row550_generated : rootPair 550 = some rowPose550 :=
  pairFieldsMatchB_sound (by decide) row550_fields
theorem row550_source : sourceKey 550 ∈ geometry.profile (sourceOwner 550) := by decide +kernel
theorem row550_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 480 key1).FastValid geometry rowPose550 := by decide +kernel
theorem row550_illegal : ¬ geometry.LegalContact rowPose550 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row550_reject_checked)
theorem row550_classified : RowClassified 550 := by
  intro p generated legal
  have he : rowPose550 = p := Option.some.inj (row550_generated.symm.trans generated)
  subst p
  exact (row550_illegal legal).elim

def rowPose551 : Pose 7 := ⟨perm74, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row551_fields : pairFieldsMatchB 188160 facet0 facet481 key0 key551 rowPose551 = true := by decide +kernel
theorem row551_generated : rootPair 551 = some rowPose551 :=
  pairFieldsMatchB_sound (by decide) row551_fields
theorem row551_source : sourceKey 551 ∈ geometry.profile (sourceOwner 551) := by decide +kernel
theorem row551_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 481 key1).FastValid geometry rowPose551 := by decide +kernel
theorem row551_illegal : ¬ geometry.LegalContact rowPose551 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row551_reject_checked)
theorem row551_classified : RowClassified 551 := by
  intro p generated legal
  have he : rowPose551 = p := Option.some.inj (row551_generated.symm.trans generated)
  subst p
  exact (row551_illegal legal).elim

def rowPose552 : Pose 7 := ⟨perm89, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row552_fields : pairFieldsMatchB 188160 facet0 facet482 key0 key552 rowPose552 = true := by decide +kernel
theorem row552_generated : rootPair 552 = some rowPose552 :=
  pairFieldsMatchB_sound (by decide) row552_fields
theorem row552_source : sourceKey 552 ∈ geometry.profile (sourceOwner 552) := by decide +kernel
theorem row552_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 482 key0).FastValid geometry rowPose552 := by decide +kernel
theorem row552_illegal : ¬ geometry.LegalContact rowPose552 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row552_reject_checked)
theorem row552_classified : RowClassified 552 := by
  intro p generated legal
  have he : rowPose552 = p := Option.some.inj (row552_generated.symm.trans generated)
  subst p
  exact (row552_illegal legal).elim

def rowPose553 : Pose 7 := ⟨perm101, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row553_fields : pairFieldsMatchB 188160 facet0 facet483 key0 key553 rowPose553 = true := by decide +kernel
theorem row553_generated : rootPair 553 = some rowPose553 :=
  pairFieldsMatchB_sound (by decide) row553_fields
theorem row553_source : sourceKey 553 ∈ geometry.profile (sourceOwner 553) := by decide +kernel
theorem row553_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 483 key1).FastValid geometry rowPose553 := by decide +kernel
theorem row553_illegal : ¬ geometry.LegalContact rowPose553 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row553_reject_checked)
theorem row553_classified : RowClassified 553 := by
  intro p generated legal
  have he : rowPose553 = p := Option.some.inj (row553_generated.symm.trans generated)
  subst p
  exact (row553_illegal legal).elim

def rowPose554 : Pose 7 := ⟨perm0, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row554_fields : pairFieldsMatchB 188160 facet0 facet484 key0 key554 rowPose554 = true := by decide +kernel
theorem row554_generated : rootPair 554 = some rowPose554 :=
  pairFieldsMatchB_sound (by decide) row554_fields
theorem row554_source : sourceKey 554 ∈ geometry.profile (sourceOwner 554) := by decide +kernel
theorem row554_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 484 key1).FastValid geometry rowPose554 := by decide +kernel
theorem row554_illegal : ¬ geometry.LegalContact rowPose554 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row554_reject_checked)
theorem row554_classified : RowClassified 554 := by
  intro p generated legal
  have he : rowPose554 = p := Option.some.inj (row554_generated.symm.trans generated)
  subst p
  exact (row554_illegal legal).elim

def rowPose555 : Pose 7 := ⟨perm21, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row555_fields : pairFieldsMatchB 188160 facet0 facet485 key0 key555 rowPose555 = true := by decide +kernel
theorem row555_generated : rootPair 555 = some rowPose555 :=
  pairFieldsMatchB_sound (by decide) row555_fields
theorem row555_source : sourceKey 555 ∈ geometry.profile (sourceOwner 555) := by decide +kernel
theorem row555_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 485 key0).FastValid geometry rowPose555 := by decide +kernel
theorem row555_illegal : ¬ geometry.LegalContact rowPose555 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row555_reject_checked)
theorem row555_classified : RowClassified 555 := by
  intro p generated legal
  have he : rowPose555 = p := Option.some.inj (row555_generated.symm.trans generated)
  subst p
  exact (row555_illegal legal).elim

def rowPose556 : Pose 7 := ⟨perm24, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row556_fields : pairFieldsMatchB 188160 facet0 facet485 key0 key556 rowPose556 = true := by decide +kernel
theorem row556_generated : rootPair 556 = some rowPose556 :=
  pairFieldsMatchB_sound (by decide) row556_fields
theorem row556_source : sourceKey 556 ∈ geometry.profile (sourceOwner 556) := by decide +kernel
theorem row556_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 36 key8).FastValid geometry rowPose556 := by decide +kernel
theorem row556_illegal : ¬ geometry.LegalContact rowPose556 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row556_reject_checked)
theorem row556_classified : RowClassified 556 := by
  intro p generated legal
  have he : rowPose556 = p := Option.some.inj (row556_generated.symm.trans generated)
  subst p
  exact (row556_illegal legal).elim

def rowPose557 : Pose 7 := ⟨perm37, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row557_fields : pairFieldsMatchB 188160 facet0 facet486 key0 key557 rowPose557 = true := by decide +kernel
theorem row557_generated : rootPair 557 = some rowPose557 :=
  pairFieldsMatchB_sound (by decide) row557_fields
theorem row557_source : sourceKey 557 ∈ geometry.profile (sourceOwner 557) := by decide +kernel
theorem row557_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 486 key0).FastValid geometry rowPose557 := by decide +kernel
theorem row557_illegal : ¬ geometry.LegalContact rowPose557 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row557_reject_checked)
theorem row557_classified : RowClassified 557 := by
  intro p generated legal
  have he : rowPose557 = p := Option.some.inj (row557_generated.symm.trans generated)
  subst p
  exact (row557_illegal legal).elim

def rowPose558 : Pose 7 := ⟨perm58, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row558_fields : pairFieldsMatchB 188160 facet0 facet487 key0 key558 rowPose558 = true := by decide +kernel
theorem row558_generated : rootPair 558 = some rowPose558 :=
  pairFieldsMatchB_sound (by decide) row558_fields
theorem row558_source : sourceKey 558 ∈ geometry.profile (sourceOwner 558) := by decide +kernel
theorem row558_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 487 key0).FastValid geometry rowPose558 := by decide +kernel
theorem row558_illegal : ¬ geometry.LegalContact rowPose558 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row558_reject_checked)
theorem row558_classified : RowClassified 558 := by
  intro p generated legal
  have he : rowPose558 = p := Option.some.inj (row558_generated.symm.trans generated)
  subst p
  exact (row558_illegal legal).elim

def rowPose559 : Pose 7 := ⟨perm71, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row559_fields : pairFieldsMatchB 188160 facet0 facet488 key0 key559 rowPose559 = true := by decide +kernel
theorem row559_generated : rootPair 559 = some rowPose559 :=
  pairFieldsMatchB_sound (by decide) row559_fields
theorem row559_source : sourceKey 559 ∈ geometry.profile (sourceOwner 559) := by decide +kernel
theorem row559_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 488 key1).FastValid geometry rowPose559 := by decide +kernel
theorem row559_illegal : ¬ geometry.LegalContact rowPose559 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row559_reject_checked)
theorem row559_classified : RowClassified 559 := by
  intro p generated legal
  have he : rowPose559 = p := Option.some.inj (row559_generated.symm.trans generated)
  subst p
  exact (row559_illegal legal).elim

def rowPose560 : Pose 7 := ⟨perm95, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row560_fields : pairFieldsMatchB 188160 facet0 facet489 key0 key560 rowPose560 = true := by decide +kernel
theorem row560_generated : rootPair 560 = some rowPose560 :=
  pairFieldsMatchB_sound (by decide) row560_fields
theorem row560_source : sourceKey 560 ∈ geometry.profile (sourceOwner 560) := by decide +kernel
theorem row560_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 489 key0).FastValid geometry rowPose560 := by decide +kernel
theorem row560_illegal : ¬ geometry.LegalContact rowPose560 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row560_reject_checked)
theorem row560_classified : RowClassified 560 := by
  intro p generated legal
  have he : rowPose560 = p := Option.some.inj (row560_generated.symm.trans generated)
  subst p
  exact (row560_illegal legal).elim

def rowPose561 : Pose 7 := ⟨perm111, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row561_fields : pairFieldsMatchB 188160 facet0 facet490 key0 key561 rowPose561 = true := by decide +kernel
theorem row561_generated : rootPair 561 = some rowPose561 :=
  pairFieldsMatchB_sound (by decide) row561_fields
theorem row561_source : sourceKey 561 ∈ geometry.profile (sourceOwner 561) := by decide +kernel
theorem row561_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 490 key1).FastValid geometry rowPose561 := by decide +kernel
theorem row561_illegal : ¬ geometry.LegalContact rowPose561 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row561_reject_checked)
theorem row561_classified : RowClassified 561 := by
  intro p generated legal
  have he : rowPose561 = p := Option.some.inj (row561_generated.symm.trans generated)
  subst p
  exact (row561_illegal legal).elim

def rowPose562 : Pose 7 := ⟨perm5, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row562_fields : pairFieldsMatchB 188160 facet0 facet491 key0 key562 rowPose562 = true := by decide +kernel
theorem row562_generated : rootPair 562 = some rowPose562 :=
  pairFieldsMatchB_sound (by decide) row562_fields
theorem row562_source : sourceKey 562 ∈ geometry.profile (sourceOwner 562) := by decide +kernel
theorem row562_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 491 key0).FastValid geometry rowPose562 := by decide +kernel
theorem row562_illegal : ¬ geometry.LegalContact rowPose562 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row562_reject_checked)
theorem row562_classified : RowClassified 562 := by
  intro p generated legal
  have he : rowPose562 = p := Option.some.inj (row562_generated.symm.trans generated)
  subst p
  exact (row562_illegal legal).elim

def rowPose563 : Pose 7 := ⟨perm21, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row563_fields : pairFieldsMatchB 188160 facet0 facet492 key0 key563 rowPose563 = true := by decide +kernel
theorem row563_generated : rootPair 563 = some rowPose563 :=
  pairFieldsMatchB_sound (by decide) row563_fields
theorem row563_source : sourceKey 563 ∈ geometry.profile (sourceOwner 563) := by decide +kernel
theorem row563_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 492 key1).FastValid geometry rowPose563 := by decide +kernel
theorem row563_illegal : ¬ geometry.LegalContact rowPose563 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row563_reject_checked)
theorem row563_classified : RowClassified 563 := by
  intro p generated legal
  have he : rowPose563 = p := Option.some.inj (row563_generated.symm.trans generated)
  subst p
  exact (row563_illegal legal).elim

def rowPose564 : Pose 7 := ⟨perm42, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row564_fields : pairFieldsMatchB 188160 facet0 facet493 key0 key564 rowPose564 = true := by decide +kernel
theorem row564_generated : rootPair 564 = some rowPose564 :=
  pairFieldsMatchB_sound (by decide) row564_fields
theorem row564_source : sourceKey 564 ∈ geometry.profile (sourceOwner 564) := by decide +kernel
theorem row564_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 493 key1).FastValid geometry rowPose564 := by decide +kernel
theorem row564_illegal : ¬ geometry.LegalContact rowPose564 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row564_reject_checked)
theorem row564_classified : RowClassified 564 := by
  intro p generated legal
  have he : rowPose564 = p := Option.some.inj (row564_generated.symm.trans generated)
  subst p
  exact (row564_illegal legal).elim

def rowPose565 : Pose 7 := ⟨perm53, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row565_fields : pairFieldsMatchB 188160 facet0 facet494 key0 key565 rowPose565 = true := by decide +kernel
theorem row565_generated : rootPair 565 = some rowPose565 :=
  pairFieldsMatchB_sound (by decide) row565_fields
theorem row565_source : sourceKey 565 ∈ geometry.profile (sourceOwner 565) := by decide +kernel
theorem row565_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 494 key0).FastValid geometry rowPose565 := by decide +kernel
theorem row565_illegal : ¬ geometry.LegalContact rowPose565 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row565_reject_checked)
theorem row565_classified : RowClassified 565 := by
  intro p generated legal
  have he : rowPose565 = p := Option.some.inj (row565_generated.symm.trans generated)
  subst p
  exact (row565_illegal legal).elim

def rowPose566 : Pose 7 := ⟨perm58, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row566_fields : pairFieldsMatchB 188160 facet0 facet494 key0 key566 rowPose566 = true := by decide +kernel
theorem row566_generated : rootPair 566 = some rowPose566 :=
  pairFieldsMatchB_sound (by decide) row566_fields
theorem row566_source : sourceKey 566 ∈ geometry.profile (sourceOwner 566) := by decide +kernel
theorem row566_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 606 key8).FastValid geometry rowPose566 := by decide +kernel
theorem row566_illegal : ¬ geometry.LegalContact rowPose566 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row566_reject_checked)
theorem row566_classified : RowClassified 566 := by
  intro p generated legal
  have he : rowPose566 = p := Option.some.inj (row566_generated.symm.trans generated)
  subst p
  exact (row566_illegal legal).elim

def rowPose567 : Pose 7 := ⟨perm69, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row567_fields : pairFieldsMatchB 188160 facet0 facet495 key0 key567 rowPose567 = true := by decide +kernel
theorem row567_generated : rootPair 567 = some rowPose567 :=
  pairFieldsMatchB_sound (by decide) row567_fields
theorem row567_source : sourceKey 567 ∈ geometry.profile (sourceOwner 567) := by decide +kernel
theorem row567_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 495 key0).FastValid geometry rowPose567 := by decide +kernel
theorem row567_illegal : ¬ geometry.LegalContact rowPose567 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row567_reject_checked)
theorem row567_classified : RowClassified 567 := by
  intro p generated legal
  have he : rowPose567 = p := Option.some.inj (row567_generated.symm.trans generated)
  subst p
  exact (row567_illegal legal).elim

def rowPose568 : Pose 7 := ⟨perm90, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row568_fields : pairFieldsMatchB 188160 facet0 facet496 key0 key568 rowPose568 = true := by decide +kernel
theorem row568_generated : rootPair 568 = some rowPose568 :=
  pairFieldsMatchB_sound (by decide) row568_fields
theorem row568_source : sourceKey 568 ∈ geometry.profile (sourceOwner 568) := by decide +kernel
theorem row568_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 496 key0).FastValid geometry rowPose568 := by decide +kernel
theorem row568_illegal : ¬ geometry.LegalContact rowPose568 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row568_reject_checked)
theorem row568_classified : RowClassified 568 := by
  intro p generated legal
  have he : rowPose568 = p := Option.some.inj (row568_generated.symm.trans generated)
  subst p
  exact (row568_illegal legal).elim

def rowPose569 : Pose 7 := ⟨perm106, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row569_fields : pairFieldsMatchB 188160 facet0 facet497 key0 key569 rowPose569 = true := by decide +kernel
theorem row569_generated : rootPair 569 = some rowPose569 :=
  pairFieldsMatchB_sound (by decide) row569_fields
theorem row569_source : sourceKey 569 ∈ geometry.profile (sourceOwner 569) := by decide +kernel
theorem row569_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 497 key1).FastValid geometry rowPose569 := by decide +kernel
theorem row569_illegal : ¬ geometry.LegalContact rowPose569 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row569_reject_checked)
theorem row569_classified : RowClassified 569 := by
  intro p generated legal
  have he : rowPose569 = p := Option.some.inj (row569_generated.symm.trans generated)
  subst p
  exact (row569_illegal legal).elim

def rowPose570 : Pose 7 := ⟨perm15, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row570_fields : pairFieldsMatchB 188160 facet0 facet498 key0 key570 rowPose570 = true := by decide +kernel
theorem row570_generated : rootPair 570 = some rowPose570 :=
  pairFieldsMatchB_sound (by decide) row570_fields
theorem row570_source : sourceKey 570 ∈ geometry.profile (sourceOwner 570) := by decide +kernel
theorem row570_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 498 key0).FastValid geometry rowPose570 := by decide +kernel
theorem row570_illegal : ¬ geometry.LegalContact rowPose570 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row570_reject_checked)
theorem row570_classified : RowClassified 570 := by
  intro p generated legal
  have he : rowPose570 = p := Option.some.inj (row570_generated.symm.trans generated)
  subst p
  exact (row570_illegal legal).elim

def rowPose571 : Pose 7 := ⟨perm24, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row571_fields : pairFieldsMatchB 188160 facet0 facet499 key0 key571 rowPose571 = true := by decide +kernel
theorem row571_generated : rootPair 571 = some rowPose571 :=
  pairFieldsMatchB_sound (by decide) row571_fields
theorem row571_source : sourceKey 571 ∈ geometry.profile (sourceOwner 571) := by decide +kernel
theorem row571_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 499 key0).FastValid geometry rowPose571 := by decide +kernel
theorem row571_illegal : ¬ geometry.LegalContact rowPose571 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row571_reject_checked)
theorem row571_classified : RowClassified 571 := by
  intro p generated legal
  have he : rowPose571 = p := Option.some.inj (row571_generated.symm.trans generated)
  subst p
  exact (row571_illegal legal).elim

def rowPose572 : Pose 7 := ⟨perm37, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row572_fields : pairFieldsMatchB 188160 facet0 facet500 key0 key572 rowPose572 = true := by decide +kernel
theorem row572_generated : rootPair 572 = some rowPose572 :=
  pairFieldsMatchB_sound (by decide) row572_fields
theorem row572_source : sourceKey 572 ∈ geometry.profile (sourceOwner 572) := by decide +kernel
theorem row572_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 556 key8).FastValid geometry rowPose572 := by decide +kernel
theorem row572_illegal : ¬ geometry.LegalContact rowPose572 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row572_reject_checked)
theorem row572_classified : RowClassified 572 := by
  intro p generated legal
  have he : rowPose572 = p := Option.some.inj (row572_generated.symm.trans generated)
  subst p
  exact (row572_illegal legal).elim

def rowPose573 : Pose 7 := ⟨perm42, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row573_fields : pairFieldsMatchB 188160 facet0 facet500 key0 key573 rowPose573 = true := by decide +kernel
theorem row573_generated : rootPair 573 = some rowPose573 :=
  pairFieldsMatchB_sound (by decide) row573_fields
theorem row573_source : sourceKey 573 ∈ geometry.profile (sourceOwner 573) := by decide +kernel
theorem row573_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 500 key0).FastValid geometry rowPose573 := by decide +kernel
theorem row573_illegal : ¬ geometry.LegalContact rowPose573 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row573_reject_checked)
theorem row573_classified : RowClassified 573 := by
  intro p generated legal
  have he : rowPose573 = p := Option.some.inj (row573_generated.symm.trans generated)
  subst p
  exact (row573_illegal legal).elim

def rowPose574 : Pose 7 := ⟨perm53, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row574_fields : pairFieldsMatchB 188160 facet0 facet501 key0 key574 rowPose574 = true := by decide +kernel
theorem row574_generated : rootPair 574 = some rowPose574 :=
  pairFieldsMatchB_sound (by decide) row574_fields
theorem row574_source : sourceKey 574 ∈ geometry.profile (sourceOwner 574) := by decide +kernel
theorem row574_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 501 key1).FastValid geometry rowPose574 := by decide +kernel
theorem row574_illegal : ¬ geometry.LegalContact rowPose574 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row574_reject_checked)
theorem row574_classified : RowClassified 574 := by
  intro p generated legal
  have he : rowPose574 = p := Option.some.inj (row574_generated.symm.trans generated)
  subst p
  exact (row574_illegal legal).elim

def rowPose575 : Pose 7 := ⟨perm74, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row575_fields : pairFieldsMatchB 188160 facet0 facet502 key0 key575 rowPose575 = true := by decide +kernel
theorem row575_generated : rootPair 575 = some rowPose575 :=
  pairFieldsMatchB_sound (by decide) row575_fields
theorem row575_source : sourceKey 575 ∈ geometry.profile (sourceOwner 575) := by decide +kernel
theorem row575_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 502 key1).FastValid geometry rowPose575 := by decide +kernel
theorem row575_illegal : ¬ geometry.LegalContact rowPose575 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row575_reject_checked)
theorem row575_classified : RowClassified 575 := by
  intro p generated legal
  have he : rowPose575 = p := Option.some.inj (row575_generated.symm.trans generated)
  subst p
  exact (row575_illegal legal).elim

theorem chunk17_classified (i : Fin 32) : RowClassified ⟨544 + i.val, by omega⟩ := by
  fin_cases i
  · exact row544_classified
  · exact row545_classified
  · exact row546_classified
  · exact row547_classified
  · exact row548_classified
  · exact row549_classified
  · exact row550_classified
  · exact row551_classified
  · exact row552_classified
  · exact row553_classified
  · exact row554_classified
  · exact row555_classified
  · exact row556_classified
  · exact row557_classified
  · exact row558_classified
  · exact row559_classified
  · exact row560_classified
  · exact row561_classified
  · exact row562_classified
  · exact row563_classified
  · exact row564_classified
  · exact row565_classified
  · exact row566_classified
  · exact row567_classified
  · exact row568_classified
  · exact row569_classified
  · exact row570_classified
  · exact row571_classified
  · exact row572_classified
  · exact row573_classified
  · exact row574_classified
  · exact row575_classified

theorem chunk17_source (i : Fin 32) : sourceKey ⟨544 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨544 + i.val, by omega⟩) := by
  fin_cases i
  · exact row544_source
  · exact row545_source
  · exact row546_source
  · exact row547_source
  · exact row548_source
  · exact row549_source
  · exact row550_source
  · exact row551_source
  · exact row552_source
  · exact row553_source
  · exact row554_source
  · exact row555_source
  · exact row556_source
  · exact row557_source
  · exact row558_source
  · exact row559_source
  · exact row560_source
  · exact row561_source
  · exact row562_source
  · exact row563_source
  · exact row564_source
  · exact row565_source
  · exact row566_source
  · exact row567_source
  · exact row568_source
  · exact row569_source
  · exact row570_source
  · exact row571_source
  · exact row572_source
  · exact row573_source
  · exact row574_source
  · exact row575_source

#print axioms chunk17_classified
end SparseMonotiles.Contact.RootZeroPilot7
