module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose608 : Pose 7 := ⟨perm87, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row608_fields : pairFieldsMatchB 188160 facet0 facet531 key0 key608 rowPose608 = true := by decide +kernel
theorem row608_generated : rootPair 608 = some rowPose608 :=
  pairFieldsMatchB_sound (by decide) row608_fields
theorem row608_source : sourceKey 608 ∈ geometry.profile (sourceOwner 608) := by decide +kernel
theorem row608_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 531 key0).FastValid geometry rowPose608 := by decide +kernel
theorem row608_illegal : ¬ geometry.LegalContact rowPose608 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row608_reject_checked)
theorem row608_classified : RowClassified 608 := by
  intro p generated legal
  have he : rowPose608 = p := Option.some.inj (row608_generated.symm.trans generated)
  subst p
  exact (row608_illegal legal).elim

def rowPose609 : Pose 7 := ⟨perm96, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row609_fields : pairFieldsMatchB 188160 facet0 facet532 key0 key609 rowPose609 = true := by decide +kernel
theorem row609_generated : rootPair 609 = some rowPose609 :=
  pairFieldsMatchB_sound (by decide) row609_fields
theorem row609_source : sourceKey 609 ∈ geometry.profile (sourceOwner 609) := by decide +kernel
theorem row609_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 532 key0).FastValid geometry rowPose609 := by decide +kernel
theorem row609_illegal : ¬ geometry.LegalContact rowPose609 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row609_reject_checked)
theorem row609_classified : RowClassified 609 := by
  intro p generated legal
  have he : rowPose609 = p := Option.some.inj (row609_generated.symm.trans generated)
  subst p
  exact (row609_illegal legal).elim

def rowPose610 : Pose 7 := ⟨perm0, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row610_fields : pairFieldsMatchB 188160 facet0 facet533 key0 key610 rowPose610 = true := by decide +kernel
theorem row610_generated : rootPair 610 = some rowPose610 :=
  pairFieldsMatchB_sound (by decide) row610_fields
theorem row610_source : sourceKey 610 ∈ geometry.profile (sourceOwner 610) := by decide +kernel
theorem row610_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 540 key8).FastValid geometry rowPose610 := by decide +kernel
theorem row610_illegal : ¬ geometry.LegalContact rowPose610 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row610_reject_checked)
theorem row610_classified : RowClassified 610 := by
  intro p generated legal
  have he : rowPose610 = p := Option.some.inj (row610_generated.symm.trans generated)
  subst p
  exact (row610_illegal legal).elim

def rowPose611 : Pose 7 := ⟨perm15, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row611_fields : pairFieldsMatchB 188160 facet0 facet533 key0 key611 rowPose611 = true := by decide +kernel
theorem row611_generated : rootPair 611 = some rowPose611 :=
  pairFieldsMatchB_sound (by decide) row611_fields
theorem row611_source : sourceKey 611 ∈ geometry.profile (sourceOwner 611) := by decide +kernel
theorem row611_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 533 key0).FastValid geometry rowPose611 := by decide +kernel
theorem row611_illegal : ¬ geometry.LegalContact rowPose611 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row611_reject_checked)
theorem row611_classified : RowClassified 611 := by
  intro p generated legal
  have he : rowPose611 = p := Option.some.inj (row611_generated.symm.trans generated)
  subst p
  exact (row611_illegal legal).elim

def rowPose612 : Pose 7 := ⟨perm21, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row612_fields : pairFieldsMatchB 188160 facet0 facet534 key0 key612 rowPose612 = true := by decide +kernel
theorem row612_generated : rootPair 612 = some rowPose612 :=
  pairFieldsMatchB_sound (by decide) row612_fields
theorem row612_source : sourceKey 612 ∈ geometry.profile (sourceOwner 612) := by decide +kernel
theorem row612_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 534 key0).FastValid geometry rowPose612 := by decide +kernel
theorem row612_illegal : ¬ geometry.LegalContact rowPose612 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row612_reject_checked)
theorem row612_classified : RowClassified 612 := by
  intro p generated legal
  have he : rowPose612 = p := Option.some.inj (row612_generated.symm.trans generated)
  subst p
  exact (row612_illegal legal).elim

def rowPose613 : Pose 7 := ⟨perm42, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row613_fields : pairFieldsMatchB 188160 facet0 facet535 key0 key613 rowPose613 = true := by decide +kernel
theorem row613_generated : rootPair 613 = some rowPose613 :=
  pairFieldsMatchB_sound (by decide) row613_fields
theorem row613_source : sourceKey 613 ∈ geometry.profile (sourceOwner 613) := by decide +kernel
theorem row613_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 535 key0).FastValid geometry rowPose613 := by decide +kernel
theorem row613_illegal : ¬ geometry.LegalContact rowPose613 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row613_reject_checked)
theorem row613_classified : RowClassified 613 := by
  intro p generated legal
  have he : rowPose613 = p := Option.some.inj (row613_generated.symm.trans generated)
  subst p
  exact (row613_illegal legal).elim

def rowPose614 : Pose 7 := ⟨perm55, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row614_fields : pairFieldsMatchB 188160 facet0 facet536 key0 key614 rowPose614 = true := by decide +kernel
theorem row614_generated : rootPair 614 = some rowPose614 :=
  pairFieldsMatchB_sound (by decide) row614_fields
theorem row614_source : sourceKey 614 ∈ geometry.profile (sourceOwner 614) := by decide +kernel
theorem row614_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 536 key1).FastValid geometry rowPose614 := by decide +kernel
theorem row614_illegal : ¬ geometry.LegalContact rowPose614 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row614_reject_checked)
theorem row614_classified : RowClassified 614 := by
  intro p generated legal
  have he : rowPose614 = p := Option.some.inj (row614_generated.symm.trans generated)
  subst p
  exact (row614_illegal legal).elim

def rowPose615 : Pose 7 := ⟨perm73, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row615_fields : pairFieldsMatchB 188160 facet0 facet537 key0 key615 rowPose615 = true := by decide +kernel
theorem row615_generated : rootPair 615 = some rowPose615 :=
  pairFieldsMatchB_sound (by decide) row615_fields
theorem row615_source : sourceKey 615 ∈ geometry.profile (sourceOwner 615) := by decide +kernel
theorem row615_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 537 key0).FastValid geometry rowPose615 := by decide +kernel
theorem row615_illegal : ¬ geometry.LegalContact rowPose615 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row615_reject_checked)
theorem row615_classified : RowClassified 615 := by
  intro p generated legal
  have he : rowPose615 = p := Option.some.inj (row615_generated.symm.trans generated)
  subst p
  exact (row615_illegal legal).elim

def rowPose616 : Pose 7 := ⟨perm87, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row616_fields : pairFieldsMatchB 188160 facet0 facet538 key0 key616 rowPose616 = true := by decide +kernel
theorem row616_generated : rootPair 616 = some rowPose616 :=
  pairFieldsMatchB_sound (by decide) row616_fields
theorem row616_source : sourceKey 616 ∈ geometry.profile (sourceOwner 616) := by decide +kernel
theorem row616_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 538 key1).FastValid geometry rowPose616 := by decide +kernel
theorem row616_illegal : ¬ geometry.LegalContact rowPose616 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row616_reject_checked)
theorem row616_classified : RowClassified 616 := by
  intro p generated legal
  have he : rowPose616 = p := Option.some.inj (row616_generated.symm.trans generated)
  subst p
  exact (row616_illegal legal).elim

def rowPose617 : Pose 7 := ⟨perm96, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row617_fields : pairFieldsMatchB 188160 facet0 facet539 key0 key617 rowPose617 = true := by decide +kernel
theorem row617_generated : rootPair 617 = some rowPose617 :=
  pairFieldsMatchB_sound (by decide) row617_fields
theorem row617_source : sourceKey 617 ∈ geometry.profile (sourceOwner 617) := by decide +kernel
theorem row617_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 539 key1).FastValid geometry rowPose617 := by decide +kernel
theorem row617_illegal : ¬ geometry.LegalContact rowPose617 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row617_reject_checked)
theorem row617_classified : RowClassified 617 := by
  intro p generated legal
  have he : rowPose617 = p := Option.some.inj (row617_generated.symm.trans generated)
  subst p
  exact (row617_illegal legal).elim

def rowPose618 : Pose 7 := ⟨perm0, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row618_fields : pairFieldsMatchB 188160 facet0 facet540 key0 key618 rowPose618 = true := by decide +kernel
theorem row618_generated : rootPair 618 = some rowPose618 :=
  pairFieldsMatchB_sound (by decide) row618_fields
theorem row618_source : sourceKey 618 ∈ geometry.profile (sourceOwner 618) := by decide +kernel
theorem row618_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 540 key1).FastValid geometry rowPose618 := by decide +kernel
theorem row618_illegal : ¬ geometry.LegalContact rowPose618 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row618_reject_checked)
theorem row618_classified : RowClassified 618 := by
  intro p generated legal
  have he : rowPose618 = p := Option.some.inj (row618_generated.symm.trans generated)
  subst p
  exact (row618_illegal legal).elim

def rowPose619 : Pose 7 := ⟨perm16, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row619_fields : pairFieldsMatchB 188160 facet0 facet541 key0 key619 rowPose619 = true := by decide +kernel
theorem row619_generated : rootPair 619 = some rowPose619 :=
  pairFieldsMatchB_sound (by decide) row619_fields
theorem row619_source : sourceKey 619 ∈ geometry.profile (sourceOwner 619) := by decide +kernel
theorem row619_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 541 key0).FastValid geometry rowPose619 := by decide +kernel
theorem row619_illegal : ¬ geometry.LegalContact rowPose619 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row619_reject_checked)
theorem row619_classified : RowClassified 619 := by
  intro p generated legal
  have he : rowPose619 = p := Option.some.inj (row619_generated.symm.trans generated)
  subst p
  exact (row619_illegal legal).elim

def rowPose620 : Pose 7 := ⟨perm40, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row620_fields : pairFieldsMatchB 188160 facet0 facet542 key0 key620 rowPose620 = true := by decide +kernel
theorem row620_generated : rootPair 620 = some rowPose620 :=
  pairFieldsMatchB_sound (by decide) row620_fields
theorem row620_source : sourceKey 620 ∈ geometry.profile (sourceOwner 620) := by decide +kernel
theorem row620_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 542 key1).FastValid geometry rowPose620 := by decide +kernel
theorem row620_illegal : ¬ geometry.LegalContact rowPose620 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row620_reject_checked)
theorem row620_classified : RowClassified 620 := by
  intro p generated legal
  have he : rowPose620 = p := Option.some.inj (row620_generated.symm.trans generated)
  subst p
  exact (row620_illegal legal).elim

def rowPose621 : Pose 7 := ⟨perm53, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row621_fields : pairFieldsMatchB 188160 facet0 facet543 key0 key621 rowPose621 = true := by decide +kernel
theorem row621_generated : rootPair 621 = some rowPose621 :=
  pairFieldsMatchB_sound (by decide) row621_fields
theorem row621_source : sourceKey 621 ∈ geometry.profile (sourceOwner 621) := by decide +kernel
theorem row621_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 543 key0).FastValid geometry rowPose621 := by decide +kernel
theorem row621_illegal : ¬ geometry.LegalContact rowPose621 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row621_reject_checked)
theorem row621_classified : RowClassified 621 := by
  intro p generated legal
  have he : rowPose621 = p := Option.some.inj (row621_generated.symm.trans generated)
  subst p
  exact (row621_illegal legal).elim

def rowPose622 : Pose 7 := ⟨perm74, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row622_fields : pairFieldsMatchB 188160 facet0 facet544 key0 key622 rowPose622 = true := by decide +kernel
theorem row622_generated : rootPair 622 = some rowPose622 :=
  pairFieldsMatchB_sound (by decide) row622_fields
theorem row622_source : sourceKey 622 ∈ geometry.profile (sourceOwner 622) := by decide +kernel
theorem row622_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 544 key0).FastValid geometry rowPose622 := by decide +kernel
theorem row622_illegal : ¬ geometry.LegalContact rowPose622 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row622_reject_checked)
theorem row622_classified : RowClassified 622 := by
  intro p generated legal
  have he : rowPose622 = p := Option.some.inj (row622_generated.symm.trans generated)
  subst p
  exact (row622_illegal legal).elim

def rowPose623 : Pose 7 := ⟨perm90, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row623_fields : pairFieldsMatchB 188160 facet0 facet545 key0 key623 rowPose623 = true := by decide +kernel
theorem row623_generated : rootPair 623 = some rowPose623 :=
  pairFieldsMatchB_sound (by decide) row623_fields
theorem row623_source : sourceKey 623 ∈ geometry.profile (sourceOwner 623) := by decide +kernel
theorem row623_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 545 key0).FastValid geometry rowPose623 := by decide +kernel
theorem row623_illegal : ¬ geometry.LegalContact rowPose623 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row623_reject_checked)
theorem row623_classified : RowClassified 623 := by
  intro p generated legal
  have he : rowPose623 = p := Option.some.inj (row623_generated.symm.trans generated)
  subst p
  exact (row623_illegal legal).elim

def rowPose624 : Pose 7 := ⟨perm87, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row624_fields : pairFieldsMatchB 188160 facet0 facet545 key0 key624 rowPose624 = true := by decide +kernel
theorem row624_generated : rootPair 624 = some rowPose624 :=
  pairFieldsMatchB_sound (by decide) row624_fields
theorem row624_source : sourceKey 624 ∈ geometry.profile (sourceOwner 624) := by decide +kernel
theorem row624_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 538 key8).FastValid geometry rowPose624 := by decide +kernel
theorem row624_illegal : ¬ geometry.LegalContact rowPose624 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row624_reject_checked)
theorem row624_classified : RowClassified 624 := by
  intro p generated legal
  have he : rowPose624 = p := Option.some.inj (row624_generated.symm.trans generated)
  subst p
  exact (row624_illegal legal).elim

def rowPose625 : Pose 7 := ⟨perm111, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row625_fields : pairFieldsMatchB 188160 facet0 facet546 key0 key625 rowPose625 = true := by decide +kernel
theorem row625_generated : rootPair 625 = some rowPose625 :=
  pairFieldsMatchB_sound (by decide) row625_fields
theorem row625_source : sourceKey 625 ∈ geometry.profile (sourceOwner 625) := by decide +kernel
theorem row625_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 546 key1).FastValid geometry rowPose625 := by decide +kernel
theorem row625_illegal : ¬ geometry.LegalContact rowPose625 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row625_reject_checked)
theorem row625_classified : RowClassified 625 := by
  intro p generated legal
  have he : rowPose625 = p := Option.some.inj (row625_generated.symm.trans generated)
  subst p
  exact (row625_illegal legal).elim

def rowPose626 : Pose 7 := ⟨perm5, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row626_fields : pairFieldsMatchB 188160 facet0 facet547 key0 key626 rowPose626 = true := by decide +kernel
theorem row626_generated : rootPair 626 = some rowPose626 :=
  pairFieldsMatchB_sound (by decide) row626_fields
theorem row626_source : sourceKey 626 ∈ geometry.profile (sourceOwner 626) := by decide +kernel
theorem row626_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 547 key1).FastValid geometry rowPose626 := by decide +kernel
theorem row626_illegal : ¬ geometry.LegalContact rowPose626 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row626_reject_checked)
theorem row626_classified : RowClassified 626 := by
  intro p generated legal
  have he : rowPose626 = p := Option.some.inj (row626_generated.symm.trans generated)
  subst p
  exact (row626_illegal legal).elim

def rowPose627 : Pose 7 := ⟨perm21, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row627_fields : pairFieldsMatchB 188160 facet0 facet548 key0 key627 rowPose627 = true := by decide +kernel
theorem row627_generated : rootPair 627 = some rowPose627 :=
  pairFieldsMatchB_sound (by decide) row627_fields
theorem row627_source : sourceKey 627 ∈ geometry.profile (sourceOwner 627) := by decide +kernel
theorem row627_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 548 key0).FastValid geometry rowPose627 := by decide +kernel
theorem row627_illegal : ¬ geometry.LegalContact rowPose627 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row627_reject_checked)
theorem row627_classified : RowClassified 627 := by
  intro p generated legal
  have he : rowPose627 = p := Option.some.inj (row627_generated.symm.trans generated)
  subst p
  exact (row627_illegal legal).elim

def rowPose628 : Pose 7 := ⟨perm42, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row628_fields : pairFieldsMatchB 188160 facet0 facet549 key0 key628 rowPose628 = true := by decide +kernel
theorem row628_generated : rootPair 628 = some rowPose628 :=
  pairFieldsMatchB_sound (by decide) row628_fields
theorem row628_source : sourceKey 628 ∈ geometry.profile (sourceOwner 628) := by decide +kernel
theorem row628_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 549 key0).FastValid geometry rowPose628 := by decide +kernel
theorem row628_illegal : ¬ geometry.LegalContact rowPose628 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row628_reject_checked)
theorem row628_classified : RowClassified 628 := by
  intro p generated legal
  have he : rowPose628 = p := Option.some.inj (row628_generated.symm.trans generated)
  subst p
  exact (row628_illegal legal).elim

def rowPose629 : Pose 7 := ⟨perm53, ![false, false, false, true, false, true, true], ![-2, 0, 0, 2, 0, 2, 2]⟩
theorem row629_fields : pairFieldsMatchB 188160 facet0 facet550 key0 key629 rowPose629 = true := by decide +kernel
theorem row629_generated : rootPair 629 = some rowPose629 :=
  pairFieldsMatchB_sound (by decide) row629_fields
theorem row629_source : sourceKey 629 ∈ geometry.profile (sourceOwner 629) := by decide +kernel
theorem row629_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 522 key8).FastValid geometry rowPose629 := by decide +kernel
theorem row629_illegal : ¬ geometry.LegalContact rowPose629 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row629_reject_checked)
theorem row629_classified : RowClassified 629 := by
  intro p generated legal
  have he : rowPose629 = p := Option.some.inj (row629_generated.symm.trans generated)
  subst p
  exact (row629_illegal legal).elim

def rowPose630 : Pose 7 := ⟨perm58, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row630_fields : pairFieldsMatchB 188160 facet0 facet550 key0 key630 rowPose630 = true := by decide +kernel
theorem row630_generated : rootPair 630 = some rowPose630 :=
  pairFieldsMatchB_sound (by decide) row630_fields
theorem row630_source : sourceKey 630 ∈ geometry.profile (sourceOwner 630) := by decide +kernel
theorem row630_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 550 key0).FastValid geometry rowPose630 := by decide +kernel
theorem row630_illegal : ¬ geometry.LegalContact rowPose630 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row630_reject_checked)
theorem row630_classified : RowClassified 630 := by
  intro p generated legal
  have he : rowPose630 = p := Option.some.inj (row630_generated.symm.trans generated)
  subst p
  exact (row630_illegal legal).elim

def rowPose631 : Pose 7 := ⟨perm69, ![false, false, false, false, false, true, false], ![-2, -1, 0, 0, -1, 1, -1]⟩
theorem row631_fields : pairFieldsMatchB 188160 facet0 facet551 key0 key631 rowPose631 = true := by decide +kernel
theorem row631_generated : rootPair 631 = some rowPose631 :=
  pairFieldsMatchB_sound (by decide) row631_fields
theorem row631_source : sourceKey 631 ∈ geometry.profile (sourceOwner 631) := by decide +kernel
theorem row631_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 551 key1).FastValid geometry rowPose631 := by decide +kernel
theorem row631_illegal : ¬ geometry.LegalContact rowPose631 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row631_reject_checked)
theorem row631_classified : RowClassified 631 := by
  intro p generated legal
  have he : rowPose631 = p := Option.some.inj (row631_generated.symm.trans generated)
  subst p
  exact (row631_illegal legal).elim

def rowPose632 : Pose 7 := ⟨perm90, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row632_fields : pairFieldsMatchB 188160 facet0 facet552 key0 key632 rowPose632 = true := by decide +kernel
theorem row632_generated : rootPair 632 = some rowPose632 :=
  pairFieldsMatchB_sound (by decide) row632_fields
theorem row632_source : sourceKey 632 ∈ geometry.profile (sourceOwner 632) := by decide +kernel
theorem row632_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 552 key1).FastValid geometry rowPose632 := by decide +kernel
theorem row632_illegal : ¬ geometry.LegalContact rowPose632 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row632_reject_checked)
theorem row632_classified : RowClassified 632 := by
  intro p generated legal
  have he : rowPose632 = p := Option.some.inj (row632_generated.symm.trans generated)
  subst p
  exact (row632_illegal legal).elim

def rowPose633 : Pose 7 := ⟨perm106, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row633_fields : pairFieldsMatchB 188160 facet0 facet553 key0 key633 rowPose633 = true := by decide +kernel
theorem row633_generated : rootPair 633 = some rowPose633 :=
  pairFieldsMatchB_sound (by decide) row633_fields
theorem row633_source : sourceKey 633 ∈ geometry.profile (sourceOwner 633) := by decide +kernel
theorem row633_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 553 key0).FastValid geometry rowPose633 := by decide +kernel
theorem row633_illegal : ¬ geometry.LegalContact rowPose633 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row633_reject_checked)
theorem row633_classified : RowClassified 633 := by
  intro p generated legal
  have he : rowPose633 = p := Option.some.inj (row633_generated.symm.trans generated)
  subst p
  exact (row633_illegal legal).elim

def rowPose634 : Pose 7 := ⟨perm0, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row634_fields : pairFieldsMatchB 188160 facet0 facet554 key0 key634 rowPose634 = true := by decide +kernel
theorem row634_generated : rootPair 634 = some rowPose634 :=
  pairFieldsMatchB_sound (by decide) row634_fields
theorem row634_source : sourceKey 634 ∈ geometry.profile (sourceOwner 634) := by decide +kernel
theorem row634_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 554 key0).FastValid geometry rowPose634 := by decide +kernel
theorem row634_illegal : ¬ geometry.LegalContact rowPose634 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row634_reject_checked)
theorem row634_classified : RowClassified 634 := by
  intro p generated legal
  have he : rowPose634 = p := Option.some.inj (row634_generated.symm.trans generated)
  subst p
  exact (row634_illegal legal).elim

def rowPose635 : Pose 7 := ⟨perm16, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row635_fields : pairFieldsMatchB 188160 facet0 facet555 key0 key635 rowPose635 = true := by decide +kernel
theorem row635_generated : rootPair 635 = some rowPose635 :=
  pairFieldsMatchB_sound (by decide) row635_fields
theorem row635_source : sourceKey 635 ∈ geometry.profile (sourceOwner 635) := by decide +kernel
theorem row635_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 555 key1).FastValid geometry rowPose635 := by decide +kernel
theorem row635_illegal : ¬ geometry.LegalContact rowPose635 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row635_reject_checked)
theorem row635_classified : RowClassified 635 := by
  intro p generated legal
  have he : rowPose635 = p := Option.some.inj (row635_generated.symm.trans generated)
  subst p
  exact (row635_illegal legal).elim

def rowPose636 : Pose 7 := ⟨perm40, ![true, false, false, true, false, true, true], ![0, -1, 0, 2, -1, 2, 2]⟩
theorem row636_fields : pairFieldsMatchB 188160 facet0 facet556 key0 key636 rowPose636 = true := by decide +kernel
theorem row636_generated : rootPair 636 = some rowPose636 :=
  pairFieldsMatchB_sound (by decide) row636_fields
theorem row636_source : sourceKey 636 ∈ geometry.profile (sourceOwner 636) := by decide +kernel
theorem row636_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 556 key0).FastValid geometry rowPose636 := by decide +kernel
theorem row636_illegal : ¬ geometry.LegalContact rowPose636 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row636_reject_checked)
theorem row636_classified : RowClassified 636 := by
  intro p generated legal
  have he : rowPose636 = p := Option.some.inj (row636_generated.symm.trans generated)
  subst p
  exact (row636_illegal legal).elim

def rowPose637 : Pose 7 := ⟨perm53, ![false, true, false, true, true, false, false], ![-2, 1, 0, 2, 2, -1, -1]⟩
theorem row637_fields : pairFieldsMatchB 188160 facet0 facet557 key0 key637 rowPose637 = true := by decide +kernel
theorem row637_generated : rootPair 637 = some rowPose637 :=
  pairFieldsMatchB_sound (by decide) row637_fields
theorem row637_source : sourceKey 637 ∈ geometry.profile (sourceOwner 637) := by decide +kernel
theorem row637_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 557 key1).FastValid geometry rowPose637 := by decide +kernel
theorem row637_illegal : ¬ geometry.LegalContact rowPose637 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row637_reject_checked)
theorem row637_classified : RowClassified 637 := by
  intro p generated legal
  have he : rowPose637 = p := Option.some.inj (row637_generated.symm.trans generated)
  subst p
  exact (row637_illegal legal).elim

def rowPose638 : Pose 7 := ⟨perm74, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row638_fields : pairFieldsMatchB 188160 facet0 facet558 key0 key638 rowPose638 = true := by decide +kernel
theorem row638_generated : rootPair 638 = some rowPose638 :=
  pairFieldsMatchB_sound (by decide) row638_fields
theorem row638_source : sourceKey 638 ∈ geometry.profile (sourceOwner 638) := by decide +kernel
theorem row638_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 558 key1).FastValid geometry rowPose638 := by decide +kernel
theorem row638_illegal : ¬ geometry.LegalContact rowPose638 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row638_reject_checked)
theorem row638_classified : RowClassified 638 := by
  intro p generated legal
  have he : rowPose638 = p := Option.some.inj (row638_generated.symm.trans generated)
  subst p
  exact (row638_illegal legal).elim

def rowPose639 : Pose 7 := ⟨perm90, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row639_fields : pairFieldsMatchB 188160 facet0 facet559 key0 key639 rowPose639 = true := by decide +kernel
theorem row639_generated : rootPair 639 = some rowPose639 :=
  pairFieldsMatchB_sound (by decide) row639_fields
theorem row639_source : sourceKey 639 ∈ geometry.profile (sourceOwner 639) := by decide +kernel
theorem row639_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 531 key8).FastValid geometry rowPose639 := by decide +kernel
theorem row639_illegal : ¬ geometry.LegalContact rowPose639 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row639_reject_checked)
theorem row639_classified : RowClassified 639 := by
  intro p generated legal
  have he : rowPose639 = p := Option.some.inj (row639_generated.symm.trans generated)
  subst p
  exact (row639_illegal legal).elim

theorem chunk19_classified (i : Fin 32) : RowClassified ⟨608 + i.val, by omega⟩ := by
  fin_cases i
  · exact row608_classified
  · exact row609_classified
  · exact row610_classified
  · exact row611_classified
  · exact row612_classified
  · exact row613_classified
  · exact row614_classified
  · exact row615_classified
  · exact row616_classified
  · exact row617_classified
  · exact row618_classified
  · exact row619_classified
  · exact row620_classified
  · exact row621_classified
  · exact row622_classified
  · exact row623_classified
  · exact row624_classified
  · exact row625_classified
  · exact row626_classified
  · exact row627_classified
  · exact row628_classified
  · exact row629_classified
  · exact row630_classified
  · exact row631_classified
  · exact row632_classified
  · exact row633_classified
  · exact row634_classified
  · exact row635_classified
  · exact row636_classified
  · exact row637_classified
  · exact row638_classified
  · exact row639_classified

theorem chunk19_source (i : Fin 32) : sourceKey ⟨608 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨608 + i.val, by omega⟩) := by
  fin_cases i
  · exact row608_source
  · exact row609_source
  · exact row610_source
  · exact row611_source
  · exact row612_source
  · exact row613_source
  · exact row614_source
  · exact row615_source
  · exact row616_source
  · exact row617_source
  · exact row618_source
  · exact row619_source
  · exact row620_source
  · exact row621_source
  · exact row622_source
  · exact row623_source
  · exact row624_source
  · exact row625_source
  · exact row626_source
  · exact row627_source
  · exact row628_source
  · exact row629_source
  · exact row630_source
  · exact row631_source
  · exact row632_source
  · exact row633_source
  · exact row634_source
  · exact row635_source
  · exact row636_source
  · exact row637_source
  · exact row638_source
  · exact row639_source

#print axioms chunk19_classified
end SparseMonotiles.Contact.RootZeroPilot7
