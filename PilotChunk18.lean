module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose576 : Pose 7 := ⟨perm89, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row576_fields : pairFieldsMatchB 188160 facet0 facet503 key0 key576 rowPose576 = true := by decide +kernel
theorem row576_generated : rootPair 576 = some rowPose576 :=
  pairFieldsMatchB_sound (by decide) row576_fields
theorem row576_source : sourceKey 576 ∈ geometry.profile (sourceOwner 576) := by decide +kernel
theorem row576_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 503 key0).FastValid geometry rowPose576 := by decide +kernel
theorem row576_illegal : ¬ geometry.LegalContact rowPose576 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row576_reject_checked)
theorem row576_classified : RowClassified 576 := by
  intro p generated legal
  have he : rowPose576 = p := Option.some.inj (row576_generated.symm.trans generated)
  subst p
  exact (row576_illegal legal).elim

def rowPose577 : Pose 7 := ⟨perm101, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row577_fields : pairFieldsMatchB 188160 facet0 facet504 key0 key577 rowPose577 = true := by decide +kernel
theorem row577_generated : rootPair 577 = some rowPose577 :=
  pairFieldsMatchB_sound (by decide) row577_fields
theorem row577_source : sourceKey 577 ∈ geometry.profile (sourceOwner 577) := by decide +kernel
theorem row577_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 504 key1).FastValid geometry rowPose577 := by decide +kernel
theorem row577_illegal : ¬ geometry.LegalContact rowPose577 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row577_reject_checked)
theorem row577_classified : RowClassified 577 := by
  intro p generated legal
  have he : rowPose577 = p := Option.some.inj (row577_generated.symm.trans generated)
  subst p
  exact (row577_illegal legal).elim

def rowPose578 : Pose 7 := ⟨perm0, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row578_fields : pairFieldsMatchB 188160 facet0 facet505 key0 key578 rowPose578 = true := by decide +kernel
theorem row578_generated : rootPair 578 = some rowPose578 :=
  pairFieldsMatchB_sound (by decide) row578_fields
theorem row578_source : sourceKey 578 ∈ geometry.profile (sourceOwner 578) := by decide +kernel
theorem row578_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 505 key1).FastValid geometry rowPose578 := by decide +kernel
theorem row578_illegal : ¬ geometry.LegalContact rowPose578 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row578_reject_checked)
theorem row578_classified : RowClassified 578 := by
  intro p generated legal
  have he : rowPose578 = p := Option.some.inj (row578_generated.symm.trans generated)
  subst p
  exact (row578_illegal legal).elim

def rowPose579 : Pose 7 := ⟨perm16, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row579_fields : pairFieldsMatchB 188160 facet0 facet506 key0 key579 rowPose579 = true := by decide +kernel
theorem row579_generated : rootPair 579 = some rowPose579 :=
  pairFieldsMatchB_sound (by decide) row579_fields
theorem row579_source : sourceKey 579 ∈ geometry.profile (sourceOwner 579) := by decide +kernel
theorem row579_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 506 key0).FastValid geometry rowPose579 := by decide +kernel
theorem row579_illegal : ¬ geometry.LegalContact rowPose579 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row579_reject_checked)
theorem row579_classified : RowClassified 579 := by
  intro p generated legal
  have he : rowPose579 = p := Option.some.inj (row579_generated.symm.trans generated)
  subst p
  exact (row579_illegal legal).elim

def rowPose580 : Pose 7 := ⟨perm40, ![true, false, false, true, true, false, false], ![0, -1, 0, 2, 1, 0, 0]⟩
theorem row580_fields : pairFieldsMatchB 188160 facet0 facet507 key0 key580 rowPose580 = true := by decide +kernel
theorem row580_generated : rootPair 580 = some rowPose580 :=
  pairFieldsMatchB_sound (by decide) row580_fields
theorem row580_source : sourceKey 580 ∈ geometry.profile (sourceOwner 580) := by decide +kernel
theorem row580_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 507 key1).FastValid geometry rowPose580 := by decide +kernel
theorem row580_illegal : ¬ geometry.LegalContact rowPose580 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row580_reject_checked)
theorem row580_classified : RowClassified 580 := by
  intro p generated legal
  have he : rowPose580 = p := Option.some.inj (row580_generated.symm.trans generated)
  subst p
  exact (row580_illegal legal).elim

def rowPose581 : Pose 7 := ⟨perm53, ![false, true, false, true, false, true, true], ![-2, 1, 0, 2, 0, 1, 1]⟩
theorem row581_fields : pairFieldsMatchB 188160 facet0 facet508 key0 key581 rowPose581 = true := by decide +kernel
theorem row581_generated : rootPair 581 = some rowPose581 :=
  pairFieldsMatchB_sound (by decide) row581_fields
theorem row581_source : sourceKey 581 ∈ geometry.profile (sourceOwner 581) := by decide +kernel
theorem row581_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 508 key0).FastValid geometry rowPose581 := by decide +kernel
theorem row581_illegal : ¬ geometry.LegalContact rowPose581 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row581_reject_checked)
theorem row581_classified : RowClassified 581 := by
  intro p generated legal
  have he : rowPose581 = p := Option.some.inj (row581_generated.symm.trans generated)
  subst p
  exact (row581_illegal legal).elim

def rowPose582 : Pose 7 := ⟨perm74, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row582_fields : pairFieldsMatchB 188160 facet0 facet509 key0 key582 rowPose582 = true := by decide +kernel
theorem row582_generated : rootPair 582 = some rowPose582 :=
  pairFieldsMatchB_sound (by decide) row582_fields
theorem row582_source : sourceKey 582 ∈ geometry.profile (sourceOwner 582) := by decide +kernel
theorem row582_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 509 key0).FastValid geometry rowPose582 := by decide +kernel
theorem row582_illegal : ¬ geometry.LegalContact rowPose582 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row582_reject_checked)
theorem row582_classified : RowClassified 582 := by
  intro p generated legal
  have he : rowPose582 = p := Option.some.inj (row582_generated.symm.trans generated)
  subst p
  exact (row582_illegal legal).elim

def rowPose583 : Pose 7 := ⟨perm90, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row583_fields : pairFieldsMatchB 188160 facet0 facet510 key0 key583 rowPose583 = true := by decide +kernel
theorem row583_generated : rootPair 583 = some rowPose583 :=
  pairFieldsMatchB_sound (by decide) row583_fields
theorem row583_source : sourceKey 583 ∈ geometry.profile (sourceOwner 583) := by decide +kernel
theorem row583_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 510 key0).FastValid geometry rowPose583 := by decide +kernel
theorem row583_illegal : ¬ geometry.LegalContact rowPose583 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row583_reject_checked)
theorem row583_classified : RowClassified 583 := by
  intro p generated legal
  have he : rowPose583 = p := Option.some.inj (row583_generated.symm.trans generated)
  subst p
  exact (row583_illegal legal).elim

def rowPose584 : Pose 7 := ⟨perm87, ![true, false, true, false, false, true, false], ![0, 0, 2, 0, 0, 2, 0]⟩
theorem row584_fields : pairFieldsMatchB 188160 facet0 facet510 key0 key584 rowPose584 = true := by decide +kernel
theorem row584_generated : rootPair 584 = some rowPose584 :=
  pairFieldsMatchB_sound (by decide) row584_fields
theorem row584_source : sourceKey 584 ∈ geometry.profile (sourceOwner 584) := by decide +kernel
theorem row584_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 517 key8).FastValid geometry rowPose584 := by decide +kernel
theorem row584_illegal : ¬ geometry.LegalContact rowPose584 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row584_reject_checked)
theorem row584_classified : RowClassified 584 := by
  intro p generated legal
  have he : rowPose584 = p := Option.some.inj (row584_generated.symm.trans generated)
  subst p
  exact (row584_illegal legal).elim

def rowPose585 : Pose 7 := ⟨perm111, ![true, true, false, true, true, true, false], ![0, 1, 0, 2, 1, 1, -1]⟩
theorem row585_fields : pairFieldsMatchB 188160 facet0 facet511 key0 key585 rowPose585 = true := by decide +kernel
theorem row585_generated : rootPair 585 = some rowPose585 :=
  pairFieldsMatchB_sound (by decide) row585_fields
theorem row585_source : sourceKey 585 ∈ geometry.profile (sourceOwner 585) := by decide +kernel
theorem row585_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 511 key1).FastValid geometry rowPose585 := by decide +kernel
theorem row585_illegal : ¬ geometry.LegalContact rowPose585 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row585_reject_checked)
theorem row585_classified : RowClassified 585 := by
  intro p generated legal
  have he : rowPose585 = p := Option.some.inj (row585_generated.symm.trans generated)
  subst p
  exact (row585_illegal legal).elim

def rowPose586 : Pose 7 := ⟨perm5, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row586_fields : pairFieldsMatchB 188160 facet0 facet512 key0 key586 rowPose586 = true := by decide +kernel
theorem row586_generated : rootPair 586 = some rowPose586 :=
  pairFieldsMatchB_sound (by decide) row586_fields
theorem row586_source : sourceKey 586 ∈ geometry.profile (sourceOwner 586) := by decide +kernel
theorem row586_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 512 key0).FastValid geometry rowPose586 := by decide +kernel
theorem row586_illegal : ¬ geometry.LegalContact rowPose586 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row586_reject_checked)
theorem row586_classified : RowClassified 586 := by
  intro p generated legal
  have he : rowPose586 = p := Option.some.inj (row586_generated.symm.trans generated)
  subst p
  exact (row586_illegal legal).elim

def rowPose587 : Pose 7 := ⟨perm21, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row587_fields : pairFieldsMatchB 188160 facet0 facet513 key0 key587 rowPose587 = true := by decide +kernel
theorem row587_generated : rootPair 587 = some rowPose587 :=
  pairFieldsMatchB_sound (by decide) row587_fields
theorem row587_source : sourceKey 587 ∈ geometry.profile (sourceOwner 587) := by decide +kernel
theorem row587_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 513 key1).FastValid geometry rowPose587 := by decide +kernel
theorem row587_illegal : ¬ geometry.LegalContact rowPose587 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row587_reject_checked)
theorem row587_classified : RowClassified 587 := by
  intro p generated legal
  have he : rowPose587 = p := Option.some.inj (row587_generated.symm.trans generated)
  subst p
  exact (row587_illegal legal).elim

def rowPose588 : Pose 7 := ⟨perm42, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row588_fields : pairFieldsMatchB 188160 facet0 facet514 key0 key588 rowPose588 = true := by decide +kernel
theorem row588_generated : rootPair 588 = some rowPose588 :=
  pairFieldsMatchB_sound (by decide) row588_fields
theorem row588_source : sourceKey 588 ∈ geometry.profile (sourceOwner 588) := by decide +kernel
theorem row588_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 514 key1).FastValid geometry rowPose588 := by decide +kernel
theorem row588_illegal : ¬ geometry.LegalContact rowPose588 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row588_reject_checked)
theorem row588_classified : RowClassified 588 := by
  intro p generated legal
  have he : rowPose588 = p := Option.some.inj (row588_generated.symm.trans generated)
  subst p
  exact (row588_illegal legal).elim

def rowPose589 : Pose 7 := ⟨perm53, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row589_fields : pairFieldsMatchB 188160 facet0 facet515 key0 key589 rowPose589 = true := by decide +kernel
theorem row589_generated : rootPair 589 = some rowPose589 :=
  pairFieldsMatchB_sound (by decide) row589_fields
theorem row589_source : sourceKey 589 ∈ geometry.profile (sourceOwner 589) := by decide +kernel
theorem row589_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 515 key0).FastValid geometry rowPose589 := by decide +kernel
theorem row589_illegal : ¬ geometry.LegalContact rowPose589 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row589_reject_checked)
theorem row589_classified : RowClassified 589 := by
  intro p generated legal
  have he : rowPose589 = p := Option.some.inj (row589_generated.symm.trans generated)
  subst p
  exact (row589_illegal legal).elim

def rowPose590 : Pose 7 := ⟨perm58, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row590_fields : pairFieldsMatchB 188160 facet0 facet515 key0 key590 rowPose590 = true := by decide +kernel
theorem row590_generated : rootPair 590 = some rowPose590 :=
  pairFieldsMatchB_sound (by decide) row590_fields
theorem row590_source : sourceKey 590 ∈ geometry.profile (sourceOwner 590) := by decide +kernel
theorem row590_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 627 key8).FastValid geometry rowPose590 := by decide +kernel
theorem row590_illegal : ¬ geometry.LegalContact rowPose590 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row590_reject_checked)
theorem row590_classified : RowClassified 590 := by
  intro p generated legal
  have he : rowPose590 = p := Option.some.inj (row590_generated.symm.trans generated)
  subst p
  exact (row590_illegal legal).elim

def rowPose591 : Pose 7 := ⟨perm69, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row591_fields : pairFieldsMatchB 188160 facet0 facet516 key0 key591 rowPose591 = true := by decide +kernel
theorem row591_generated : rootPair 591 = some rowPose591 :=
  pairFieldsMatchB_sound (by decide) row591_fields
theorem row591_source : sourceKey 591 ∈ geometry.profile (sourceOwner 591) := by decide +kernel
theorem row591_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 516 key0).FastValid geometry rowPose591 := by decide +kernel
theorem row591_illegal : ¬ geometry.LegalContact rowPose591 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row591_reject_checked)
theorem row591_classified : RowClassified 591 := by
  intro p generated legal
  have he : rowPose591 = p := Option.some.inj (row591_generated.symm.trans generated)
  subst p
  exact (row591_illegal legal).elim

def rowPose592 : Pose 7 := ⟨perm90, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row592_fields : pairFieldsMatchB 188160 facet0 facet517 key0 key592 rowPose592 = true := by decide +kernel
theorem row592_generated : rootPair 592 = some rowPose592 :=
  pairFieldsMatchB_sound (by decide) row592_fields
theorem row592_source : sourceKey 592 ∈ geometry.profile (sourceOwner 592) := by decide +kernel
theorem row592_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 517 key0).FastValid geometry rowPose592 := by decide +kernel
theorem row592_illegal : ¬ geometry.LegalContact rowPose592 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row592_reject_checked)
theorem row592_classified : RowClassified 592 := by
  intro p generated legal
  have he : rowPose592 = p := Option.some.inj (row592_generated.symm.trans generated)
  subst p
  exact (row592_illegal legal).elim

def rowPose593 : Pose 7 := ⟨perm106, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row593_fields : pairFieldsMatchB 188160 facet0 facet518 key0 key593 rowPose593 = true := by decide +kernel
theorem row593_generated : rootPair 593 = some rowPose593 :=
  pairFieldsMatchB_sound (by decide) row593_fields
theorem row593_source : sourceKey 593 ∈ geometry.profile (sourceOwner 593) := by decide +kernel
theorem row593_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 518 key1).FastValid geometry rowPose593 := by decide +kernel
theorem row593_illegal : ¬ geometry.LegalContact rowPose593 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row593_reject_checked)
theorem row593_classified : RowClassified 593 := by
  intro p generated legal
  have he : rowPose593 = p := Option.some.inj (row593_generated.symm.trans generated)
  subst p
  exact (row593_illegal legal).elim

def rowPose594 : Pose 7 := ⟨perm0, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row594_fields : pairFieldsMatchB 188160 facet0 facet519 key0 key594 rowPose594 = true := by decide +kernel
theorem row594_generated : rootPair 594 = some rowPose594 :=
  pairFieldsMatchB_sound (by decide) row594_fields
theorem row594_source : sourceKey 594 ∈ geometry.profile (sourceOwner 594) := by decide +kernel
theorem row594_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 519 key0).FastValid geometry rowPose594 := by decide +kernel
theorem row594_illegal : ¬ geometry.LegalContact rowPose594 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row594_reject_checked)
theorem row594_classified : RowClassified 594 := by
  intro p generated legal
  have he : rowPose594 = p := Option.some.inj (row594_generated.symm.trans generated)
  subst p
  exact (row594_illegal legal).elim

def rowPose595 : Pose 7 := ⟨perm16, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row595_fields : pairFieldsMatchB 188160 facet0 facet520 key0 key595 rowPose595 = true := by decide +kernel
theorem row595_generated : rootPair 595 = some rowPose595 :=
  pairFieldsMatchB_sound (by decide) row595_fields
theorem row595_source : sourceKey 595 ∈ geometry.profile (sourceOwner 595) := by decide +kernel
theorem row595_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 520 key1).FastValid geometry rowPose595 := by decide +kernel
theorem row595_illegal : ¬ geometry.LegalContact rowPose595 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row595_reject_checked)
theorem row595_classified : RowClassified 595 := by
  intro p generated legal
  have he : rowPose595 = p := Option.some.inj (row595_generated.symm.trans generated)
  subst p
  exact (row595_illegal legal).elim

def rowPose596 : Pose 7 := ⟨perm40, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row596_fields : pairFieldsMatchB 188160 facet0 facet521 key0 key596 rowPose596 = true := by decide +kernel
theorem row596_generated : rootPair 596 = some rowPose596 :=
  pairFieldsMatchB_sound (by decide) row596_fields
theorem row596_source : sourceKey 596 ∈ geometry.profile (sourceOwner 596) := by decide +kernel
theorem row596_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 521 key0).FastValid geometry rowPose596 := by decide +kernel
theorem row596_illegal : ¬ geometry.LegalContact rowPose596 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row596_reject_checked)
theorem row596_classified : RowClassified 596 := by
  intro p generated legal
  have he : rowPose596 = p := Option.some.inj (row596_generated.symm.trans generated)
  subst p
  exact (row596_illegal legal).elim

def rowPose597 : Pose 7 := ⟨perm53, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row597_fields : pairFieldsMatchB 188160 facet0 facet522 key0 key597 rowPose597 = true := by decide +kernel
theorem row597_generated : rootPair 597 = some rowPose597 :=
  pairFieldsMatchB_sound (by decide) row597_fields
theorem row597_source : sourceKey 597 ∈ geometry.profile (sourceOwner 597) := by decide +kernel
theorem row597_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 522 key1).FastValid geometry rowPose597 := by decide +kernel
theorem row597_illegal : ¬ geometry.LegalContact rowPose597 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row597_reject_checked)
theorem row597_classified : RowClassified 597 := by
  intro p generated legal
  have he : rowPose597 = p := Option.some.inj (row597_generated.symm.trans generated)
  subst p
  exact (row597_illegal legal).elim

def rowPose598 : Pose 7 := ⟨perm74, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row598_fields : pairFieldsMatchB 188160 facet0 facet523 key0 key598 rowPose598 = true := by decide +kernel
theorem row598_generated : rootPair 598 = some rowPose598 :=
  pairFieldsMatchB_sound (by decide) row598_fields
theorem row598_source : sourceKey 598 ∈ geometry.profile (sourceOwner 598) := by decide +kernel
theorem row598_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 523 key1).FastValid geometry rowPose598 := by decide +kernel
theorem row598_illegal : ¬ geometry.LegalContact rowPose598 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row598_reject_checked)
theorem row598_classified : RowClassified 598 := by
  intro p generated legal
  have he : rowPose598 = p := Option.some.inj (row598_generated.symm.trans generated)
  subst p
  exact (row598_illegal legal).elim

def rowPose599 : Pose 7 := ⟨perm90, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row599_fields : pairFieldsMatchB 188160 facet0 facet524 key0 key599 rowPose599 = true := by decide +kernel
theorem row599_generated : rootPair 599 = some rowPose599 :=
  pairFieldsMatchB_sound (by decide) row599_fields
theorem row599_source : sourceKey 599 ∈ geometry.profile (sourceOwner 599) := by decide +kernel
theorem row599_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 552 key8).FastValid geometry rowPose599 := by decide +kernel
theorem row599_illegal : ¬ geometry.LegalContact rowPose599 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row599_reject_checked)
theorem row599_classified : RowClassified 599 := by
  intro p generated legal
  have he : rowPose599 = p := Option.some.inj (row599_generated.symm.trans generated)
  subst p
  exact (row599_illegal legal).elim

def rowPose600 : Pose 7 := ⟨perm87, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row600_fields : pairFieldsMatchB 188160 facet0 facet524 key0 key600 rowPose600 = true := by decide +kernel
theorem row600_generated : rootPair 600 = some rowPose600 :=
  pairFieldsMatchB_sound (by decide) row600_fields
theorem row600_source : sourceKey 600 ∈ geometry.profile (sourceOwner 600) := by decide +kernel
theorem row600_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 524 key0).FastValid geometry rowPose600 := by decide +kernel
theorem row600_illegal : ¬ geometry.LegalContact rowPose600 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row600_reject_checked)
theorem row600_classified : RowClassified 600 := by
  intro p generated legal
  have he : rowPose600 = p := Option.some.inj (row600_generated.symm.trans generated)
  subst p
  exact (row600_illegal legal).elim

def rowPose601 : Pose 7 := ⟨perm111, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row601_fields : pairFieldsMatchB 188160 facet0 facet525 key0 key601 rowPose601 = true := by decide +kernel
theorem row601_generated : rootPair 601 = some rowPose601 :=
  pairFieldsMatchB_sound (by decide) row601_fields
theorem row601_source : sourceKey 601 ∈ geometry.profile (sourceOwner 601) := by decide +kernel
theorem row601_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 525 key0).FastValid geometry rowPose601 := by decide +kernel
theorem row601_illegal : ¬ geometry.LegalContact rowPose601 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row601_reject_checked)
theorem row601_classified : RowClassified 601 := by
  intro p generated legal
  have he : rowPose601 = p := Option.some.inj (row601_generated.symm.trans generated)
  subst p
  exact (row601_illegal legal).elim

def rowPose602 : Pose 7 := ⟨perm0, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row602_fields : pairFieldsMatchB 188160 facet0 facet526 key0 key602 rowPose602 = true := by decide +kernel
theorem row602_generated : rootPair 602 = some rowPose602 :=
  pairFieldsMatchB_sound (by decide) row602_fields
theorem row602_source : sourceKey 602 ∈ geometry.profile (sourceOwner 602) := by decide +kernel
theorem row602_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 526 key0).FastValid geometry rowPose602 := by decide +kernel
theorem row602_illegal : ¬ geometry.LegalContact rowPose602 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row602_reject_checked)
theorem row602_classified : RowClassified 602 := by
  intro p generated legal
  have he : rowPose602 = p := Option.some.inj (row602_generated.symm.trans generated)
  subst p
  exact (row602_illegal legal).elim

def rowPose603 : Pose 7 := ⟨perm15, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row603_fields : pairFieldsMatchB 188160 facet0 facet526 key0 key603 rowPose603 = true := by decide +kernel
theorem row603_generated : rootPair 603 = some rowPose603 :=
  pairFieldsMatchB_sound (by decide) row603_fields
theorem row603_source : sourceKey 603 ∈ geometry.profile (sourceOwner 603) := by decide +kernel
theorem row603_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 751 key8).FastValid geometry rowPose603 := by decide +kernel
theorem row603_illegal : ¬ geometry.LegalContact rowPose603 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row603_reject_checked)
theorem row603_classified : RowClassified 603 := by
  intro p generated legal
  have he : rowPose603 = p := Option.some.inj (row603_generated.symm.trans generated)
  subst p
  exact (row603_illegal legal).elim

def rowPose604 : Pose 7 := ⟨perm21, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row604_fields : pairFieldsMatchB 188160 facet0 facet527 key0 key604 rowPose604 = true := by decide +kernel
theorem row604_generated : rootPair 604 = some rowPose604 :=
  pairFieldsMatchB_sound (by decide) row604_fields
theorem row604_source : sourceKey 604 ∈ geometry.profile (sourceOwner 604) := by decide +kernel
theorem row604_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 527 key1).FastValid geometry rowPose604 := by decide +kernel
theorem row604_illegal : ¬ geometry.LegalContact rowPose604 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row604_reject_checked)
theorem row604_classified : RowClassified 604 := by
  intro p generated legal
  have he : rowPose604 = p := Option.some.inj (row604_generated.symm.trans generated)
  subst p
  exact (row604_illegal legal).elim

def rowPose605 : Pose 7 := ⟨perm42, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row605_fields : pairFieldsMatchB 188160 facet0 facet528 key0 key605 rowPose605 = true := by decide +kernel
theorem row605_generated : rootPair 605 = some rowPose605 :=
  pairFieldsMatchB_sound (by decide) row605_fields
theorem row605_source : sourceKey 605 ∈ geometry.profile (sourceOwner 605) := by decide +kernel
theorem row605_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 528 key1).FastValid geometry rowPose605 := by decide +kernel
theorem row605_illegal : ¬ geometry.LegalContact rowPose605 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row605_reject_checked)
theorem row605_classified : RowClassified 605 := by
  intro p generated legal
  have he : rowPose605 = p := Option.some.inj (row605_generated.symm.trans generated)
  subst p
  exact (row605_illegal legal).elim

def rowPose606 : Pose 7 := ⟨perm55, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row606_fields : pairFieldsMatchB 188160 facet0 facet529 key0 key606 rowPose606 = true := by decide +kernel
theorem row606_generated : rootPair 606 = some rowPose606 :=
  pairFieldsMatchB_sound (by decide) row606_fields
theorem row606_source : sourceKey 606 ∈ geometry.profile (sourceOwner 606) := by decide +kernel
theorem row606_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 529 key0).FastValid geometry rowPose606 := by decide +kernel
theorem row606_illegal : ¬ geometry.LegalContact rowPose606 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row606_reject_checked)
theorem row606_classified : RowClassified 606 := by
  intro p generated legal
  have he : rowPose606 = p := Option.some.inj (row606_generated.symm.trans generated)
  subst p
  exact (row606_illegal legal).elim

def rowPose607 : Pose 7 := ⟨perm73, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row607_fields : pairFieldsMatchB 188160 facet0 facet530 key0 key607 rowPose607 = true := by decide +kernel
theorem row607_generated : rootPair 607 = some rowPose607 :=
  pairFieldsMatchB_sound (by decide) row607_fields
theorem row607_source : sourceKey 607 ∈ geometry.profile (sourceOwner 607) := by decide +kernel
theorem row607_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 530 key1).FastValid geometry rowPose607 := by decide +kernel
theorem row607_illegal : ¬ geometry.LegalContact rowPose607 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row607_reject_checked)
theorem row607_classified : RowClassified 607 := by
  intro p generated legal
  have he : rowPose607 = p := Option.some.inj (row607_generated.symm.trans generated)
  subst p
  exact (row607_illegal legal).elim

theorem chunk18_classified (i : Fin 32) : RowClassified ⟨576 + i.val, by omega⟩ := by
  fin_cases i
  · exact row576_classified
  · exact row577_classified
  · exact row578_classified
  · exact row579_classified
  · exact row580_classified
  · exact row581_classified
  · exact row582_classified
  · exact row583_classified
  · exact row584_classified
  · exact row585_classified
  · exact row586_classified
  · exact row587_classified
  · exact row588_classified
  · exact row589_classified
  · exact row590_classified
  · exact row591_classified
  · exact row592_classified
  · exact row593_classified
  · exact row594_classified
  · exact row595_classified
  · exact row596_classified
  · exact row597_classified
  · exact row598_classified
  · exact row599_classified
  · exact row600_classified
  · exact row601_classified
  · exact row602_classified
  · exact row603_classified
  · exact row604_classified
  · exact row605_classified
  · exact row606_classified
  · exact row607_classified

theorem chunk18_source (i : Fin 32) : sourceKey ⟨576 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨576 + i.val, by omega⟩) := by
  fin_cases i
  · exact row576_source
  · exact row577_source
  · exact row578_source
  · exact row579_source
  · exact row580_source
  · exact row581_source
  · exact row582_source
  · exact row583_source
  · exact row584_source
  · exact row585_source
  · exact row586_source
  · exact row587_source
  · exact row588_source
  · exact row589_source
  · exact row590_source
  · exact row591_source
  · exact row592_source
  · exact row593_source
  · exact row594_source
  · exact row595_source
  · exact row596_source
  · exact row597_source
  · exact row598_source
  · exact row599_source
  · exact row600_source
  · exact row601_source
  · exact row602_source
  · exact row603_source
  · exact row604_source
  · exact row605_source
  · exact row606_source
  · exact row607_source

#print axioms chunk18_classified
end SparseMonotiles.Contact.RootZeroPilot7
