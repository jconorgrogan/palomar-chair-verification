module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose640 : Pose 7 := ⟨perm87, ![false, true, true, false, false, true, true], ![-2, 2, 2, 0, 0, 2, 2]⟩
theorem row640_fields : pairFieldsMatchB 188160 facet0 facet559 key0 key640 rowPose640 = true := by decide +kernel
theorem row640_generated : rootPair 640 = some rowPose640 :=
  pairFieldsMatchB_sound (by decide) row640_fields
theorem row640_source : sourceKey 640 ∈ geometry.profile (sourceOwner 640) := by decide +kernel
theorem row640_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 559 key0).FastValid geometry rowPose640 := by decide +kernel
theorem row640_illegal : ¬ geometry.LegalContact rowPose640 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row640_reject_checked)
theorem row640_classified : RowClassified 640 := by
  intro p generated legal
  have he : rowPose640 = p := Option.some.inj (row640_generated.symm.trans generated)
  subst p
  exact (row640_illegal legal).elim

def rowPose641 : Pose 7 := ⟨perm111, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 1, -1]⟩
theorem row641_fields : pairFieldsMatchB 188160 facet0 facet560 key0 key641 rowPose641 = true := by decide +kernel
theorem row641_generated : rootPair 641 = some rowPose641 :=
  pairFieldsMatchB_sound (by decide) row641_fields
theorem row641_source : sourceKey 641 ∈ geometry.profile (sourceOwner 641) := by decide +kernel
theorem row641_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 560 key0).FastValid geometry rowPose641 := by decide +kernel
theorem row641_illegal : ¬ geometry.LegalContact rowPose641 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row641_reject_checked)
theorem row641_classified : RowClassified 641 := by
  intro p generated legal
  have he : rowPose641 = p := Option.some.inj (row641_generated.symm.trans generated)
  subst p
  exact (row641_illegal legal).elim

def rowPose642 : Pose 7 := ⟨perm0, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row642_fields : pairFieldsMatchB 188160 facet0 facet561 key0 key642 rowPose642 = true := by decide +kernel
theorem row642_generated : rootPair 642 = some rowPose642 :=
  pairFieldsMatchB_sound (by decide) row642_fields
theorem row642_source : sourceKey 642 ∈ geometry.profile (sourceOwner 642) := by decide +kernel
theorem row642_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 561 key0).FastValid geometry rowPose642 := by decide +kernel
theorem row642_illegal : ¬ geometry.LegalContact rowPose642 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row642_reject_checked)
theorem row642_classified : RowClassified 642 := by
  intro p generated legal
  have he : rowPose642 = p := Option.some.inj (row642_generated.symm.trans generated)
  subst p
  exact (row642_illegal legal).elim

def rowPose643 : Pose 7 := ⟨perm21, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row643_fields : pairFieldsMatchB 188160 facet0 facet562 key0 key643 rowPose643 = true := by decide +kernel
theorem row643_generated : rootPair 643 = some rowPose643 :=
  pairFieldsMatchB_sound (by decide) row643_fields
theorem row643_source : sourceKey 643 ∈ geometry.profile (sourceOwner 643) := by decide +kernel
theorem row643_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 450 key8).FastValid geometry rowPose643 := by decide +kernel
theorem row643_illegal : ¬ geometry.LegalContact rowPose643 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row643_reject_checked)
theorem row643_classified : RowClassified 643 := by
  intro p generated legal
  have he : rowPose643 = p := Option.some.inj (row643_generated.symm.trans generated)
  subst p
  exact (row643_illegal legal).elim

def rowPose644 : Pose 7 := ⟨perm24, ![true, true, false, false, false, false, true], ![0, 2, 0, 0, 0, 0, 2]⟩
theorem row644_fields : pairFieldsMatchB 188160 facet0 facet562 key0 key644 rowPose644 = true := by decide +kernel
theorem row644_generated : rootPair 644 = some rowPose644 :=
  pairFieldsMatchB_sound (by decide) row644_fields
theorem row644_source : sourceKey 644 ∈ geometry.profile (sourceOwner 644) := by decide +kernel
theorem row644_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 562 key0).FastValid geometry rowPose644 := by decide +kernel
theorem row644_illegal : ¬ geometry.LegalContact rowPose644 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row644_reject_checked)
theorem row644_classified : RowClassified 644 := by
  intro p generated legal
  have he : rowPose644 = p := Option.some.inj (row644_generated.symm.trans generated)
  subst p
  exact (row644_illegal legal).elim

def rowPose645 : Pose 7 := ⟨perm37, ![false, true, true, false, true, true, true], ![-2, 1, 2, 0, 1, 1, 1]⟩
theorem row645_fields : pairFieldsMatchB 188160 facet0 facet563 key0 key645 rowPose645 = true := by decide +kernel
theorem row645_generated : rootPair 645 = some rowPose645 :=
  pairFieldsMatchB_sound (by decide) row645_fields
theorem row645_source : sourceKey 645 ∈ geometry.profile (sourceOwner 645) := by decide +kernel
theorem row645_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 563 key1).FastValid geometry rowPose645 := by decide +kernel
theorem row645_illegal : ¬ geometry.LegalContact rowPose645 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row645_reject_checked)
theorem row645_classified : RowClassified 645 := by
  intro p generated legal
  have he : rowPose645 = p := Option.some.inj (row645_generated.symm.trans generated)
  subst p
  exact (row645_illegal legal).elim

def rowPose646 : Pose 7 := ⟨perm58, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row646_fields : pairFieldsMatchB 188160 facet0 facet564 key0 key646 rowPose646 = true := by decide +kernel
theorem row646_generated : rootPair 646 = some rowPose646 :=
  pairFieldsMatchB_sound (by decide) row646_fields
theorem row646_source : sourceKey 646 ∈ geometry.profile (sourceOwner 646) := by decide +kernel
theorem row646_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 564 key1).FastValid geometry rowPose646 := by decide +kernel
theorem row646_illegal : ¬ geometry.LegalContact rowPose646 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row646_reject_checked)
theorem row646_classified : RowClassified 646 := by
  intro p generated legal
  have he : rowPose646 = p := Option.some.inj (row646_generated.symm.trans generated)
  subst p
  exact (row646_illegal legal).elim

def rowPose647 : Pose 7 := ⟨perm71, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row647_fields : pairFieldsMatchB 188160 facet0 facet565 key0 key647 rowPose647 = true := by decide +kernel
theorem row647_generated : rootPair 647 = some rowPose647 :=
  pairFieldsMatchB_sound (by decide) row647_fields
theorem row647_source : sourceKey 647 ∈ geometry.profile (sourceOwner 647) := by decide +kernel
theorem row647_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 565 key0).FastValid geometry rowPose647 := by decide +kernel
theorem row647_illegal : ¬ geometry.LegalContact rowPose647 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row647_reject_checked)
theorem row647_classified : RowClassified 647 := by
  intro p generated legal
  have he : rowPose647 = p := Option.some.inj (row647_generated.symm.trans generated)
  subst p
  exact (row647_illegal legal).elim

def rowPose648 : Pose 7 := ⟨perm95, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, 0, 2]⟩
theorem row648_fields : pairFieldsMatchB 188160 facet0 facet566 key0 key648 rowPose648 = true := by decide +kernel
theorem row648_generated : rootPair 648 = some rowPose648 :=
  pairFieldsMatchB_sound (by decide) row648_fields
theorem row648_source : sourceKey 648 ∈ geometry.profile (sourceOwner 648) := by decide +kernel
theorem row648_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 566 key1).FastValid geometry rowPose648 := by decide +kernel
theorem row648_illegal : ¬ geometry.LegalContact rowPose648 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row648_reject_checked)
theorem row648_classified : RowClassified 648 := by
  intro p generated legal
  have he : rowPose648 = p := Option.some.inj (row648_generated.symm.trans generated)
  subst p
  exact (row648_illegal legal).elim

def rowPose649 : Pose 7 := ⟨perm111, ![true, true, false, false, true, true, false], ![0, 1, 0, 0, 2, 1, -1]⟩
theorem row649_fields : pairFieldsMatchB 188160 facet0 facet567 key0 key649 rowPose649 = true := by decide +kernel
theorem row649_generated : rootPair 649 = some rowPose649 :=
  pairFieldsMatchB_sound (by decide) row649_fields
theorem row649_source : sourceKey 649 ∈ geometry.profile (sourceOwner 649) := by decide +kernel
theorem row649_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 567 key0).FastValid geometry rowPose649 := by decide +kernel
theorem row649_illegal : ¬ geometry.LegalContact rowPose649 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row649_reject_checked)
theorem row649_classified : RowClassified 649 := by
  intro p generated legal
  have he : rowPose649 = p := Option.some.inj (row649_generated.symm.trans generated)
  subst p
  exact (row649_illegal legal).elim

def rowPose650 : Pose 7 := ⟨perm0, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row650_fields : pairFieldsMatchB 188160 facet0 facet568 key0 key650 rowPose650 = true := by decide +kernel
theorem row650_generated : rootPair 650 = some rowPose650 :=
  pairFieldsMatchB_sound (by decide) row650_fields
theorem row650_source : sourceKey 650 ∈ geometry.profile (sourceOwner 650) := by decide +kernel
theorem row650_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 568 key0).FastValid geometry rowPose650 := by decide +kernel
theorem row650_illegal : ¬ geometry.LegalContact rowPose650 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row650_reject_checked)
theorem row650_classified : RowClassified 650 := by
  intro p generated legal
  have he : rowPose650 = p := Option.some.inj (row650_generated.symm.trans generated)
  subst p
  exact (row650_illegal legal).elim

def rowPose651 : Pose 7 := ⟨perm16, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row651_fields : pairFieldsMatchB 188160 facet0 facet569 key0 key651 rowPose651 = true := by decide +kernel
theorem row651_generated : rootPair 651 = some rowPose651 :=
  pairFieldsMatchB_sound (by decide) row651_fields
theorem row651_source : sourceKey 651 ∈ geometry.profile (sourceOwner 651) := by decide +kernel
theorem row651_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 569 key1).FastValid geometry rowPose651 := by decide +kernel
theorem row651_illegal : ¬ geometry.LegalContact rowPose651 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row651_reject_checked)
theorem row651_classified : RowClassified 651 := by
  intro p generated legal
  have he : rowPose651 = p := Option.some.inj (row651_generated.symm.trans generated)
  subst p
  exact (row651_illegal legal).elim

def rowPose652 : Pose 7 := ⟨perm40, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row652_fields : pairFieldsMatchB 188160 facet0 facet570 key0 key652 rowPose652 = true := by decide +kernel
theorem row652_generated : rootPair 652 = some rowPose652 :=
  pairFieldsMatchB_sound (by decide) row652_fields
theorem row652_source : sourceKey 652 ∈ geometry.profile (sourceOwner 652) := by decide +kernel
theorem row652_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 570 key0).FastValid geometry rowPose652 := by decide +kernel
theorem row652_illegal : ¬ geometry.LegalContact rowPose652 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row652_reject_checked)
theorem row652_classified : RowClassified 652 := by
  intro p generated legal
  have he : rowPose652 = p := Option.some.inj (row652_generated.symm.trans generated)
  subst p
  exact (row652_illegal legal).elim

def rowPose653 : Pose 7 := ⟨perm53, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row653_fields : pairFieldsMatchB 188160 facet0 facet571 key0 key653 rowPose653 = true := by decide +kernel
theorem row653_generated : rootPair 653 = some rowPose653 :=
  pairFieldsMatchB_sound (by decide) row653_fields
theorem row653_source : sourceKey 653 ∈ geometry.profile (sourceOwner 653) := by decide +kernel
theorem row653_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 571 key1).FastValid geometry rowPose653 := by decide +kernel
theorem row653_illegal : ¬ geometry.LegalContact rowPose653 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row653_reject_checked)
theorem row653_classified : RowClassified 653 := by
  intro p generated legal
  have he : rowPose653 = p := Option.some.inj (row653_generated.symm.trans generated)
  subst p
  exact (row653_illegal legal).elim

def rowPose654 : Pose 7 := ⟨perm74, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row654_fields : pairFieldsMatchB 188160 facet0 facet572 key0 key654 rowPose654 = true := by decide +kernel
theorem row654_generated : rootPair 654 = some rowPose654 :=
  pairFieldsMatchB_sound (by decide) row654_fields
theorem row654_source : sourceKey 654 ∈ geometry.profile (sourceOwner 654) := by decide +kernel
theorem row654_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 572 key1).FastValid geometry rowPose654 := by decide +kernel
theorem row654_illegal : ¬ geometry.LegalContact rowPose654 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row654_reject_checked)
theorem row654_classified : RowClassified 654 := by
  intro p generated legal
  have he : rowPose654 = p := Option.some.inj (row654_generated.symm.trans generated)
  subst p
  exact (row654_illegal legal).elim

def rowPose655 : Pose 7 := ⟨perm90, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row655_fields : pairFieldsMatchB 188160 facet0 facet573 key0 key655 rowPose655 = true := by decide +kernel
theorem row655_generated : rootPair 655 = some rowPose655 :=
  pairFieldsMatchB_sound (by decide) row655_fields
theorem row655_source : sourceKey 655 ∈ geometry.profile (sourceOwner 655) := by decide +kernel
theorem row655_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 601 key8).FastValid geometry rowPose655 := by decide +kernel
theorem row655_illegal : ¬ geometry.LegalContact rowPose655 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row655_reject_checked)
theorem row655_classified : RowClassified 655 := by
  intro p generated legal
  have he : rowPose655 = p := Option.some.inj (row655_generated.symm.trans generated)
  subst p
  exact (row655_illegal legal).elim

def rowPose656 : Pose 7 := ⟨perm87, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row656_fields : pairFieldsMatchB 188160 facet0 facet573 key0 key656 rowPose656 = true := by decide +kernel
theorem row656_generated : rootPair 656 = some rowPose656 :=
  pairFieldsMatchB_sound (by decide) row656_fields
theorem row656_source : sourceKey 656 ∈ geometry.profile (sourceOwner 656) := by decide +kernel
theorem row656_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 573 key0).FastValid geometry rowPose656 := by decide +kernel
theorem row656_illegal : ¬ geometry.LegalContact rowPose656 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row656_reject_checked)
theorem row656_classified : RowClassified 656 := by
  intro p generated legal
  have he : rowPose656 = p := Option.some.inj (row656_generated.symm.trans generated)
  subst p
  exact (row656_illegal legal).elim

def rowPose657 : Pose 7 := ⟨perm111, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row657_fields : pairFieldsMatchB 188160 facet0 facet574 key0 key657 rowPose657 = true := by decide +kernel
theorem row657_generated : rootPair 657 = some rowPose657 :=
  pairFieldsMatchB_sound (by decide) row657_fields
theorem row657_source : sourceKey 657 ∈ geometry.profile (sourceOwner 657) := by decide +kernel
theorem row657_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 574 key0).FastValid geometry rowPose657 := by decide +kernel
theorem row657_illegal : ¬ geometry.LegalContact rowPose657 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row657_reject_checked)
theorem row657_classified : RowClassified 657 := by
  intro p generated legal
  have he : rowPose657 = p := Option.some.inj (row657_generated.symm.trans generated)
  subst p
  exact (row657_illegal legal).elim

def rowPose658 : Pose 7 := ⟨perm0, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row658_fields : pairFieldsMatchB 188160 facet0 facet575 key0 key658 rowPose658 = true := by decide +kernel
theorem row658_generated : rootPair 658 = some rowPose658 :=
  pairFieldsMatchB_sound (by decide) row658_fields
theorem row658_source : sourceKey 658 ∈ geometry.profile (sourceOwner 658) := by decide +kernel
theorem row658_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 582 key8).FastValid geometry rowPose658 := by decide +kernel
theorem row658_illegal : ¬ geometry.LegalContact rowPose658 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row658_reject_checked)
theorem row658_classified : RowClassified 658 := by
  intro p generated legal
  have he : rowPose658 = p := Option.some.inj (row658_generated.symm.trans generated)
  subst p
  exact (row658_illegal legal).elim

def rowPose659 : Pose 7 := ⟨perm15, ![false, false, true, false, false, true, false], ![-2, 0, 2, 0, 0, 2, 0]⟩
theorem row659_fields : pairFieldsMatchB 188160 facet0 facet575 key0 key659 rowPose659 = true := by decide +kernel
theorem row659_generated : rootPair 659 = some rowPose659 :=
  pairFieldsMatchB_sound (by decide) row659_fields
theorem row659_source : sourceKey 659 ∈ geometry.profile (sourceOwner 659) := by decide +kernel
theorem row659_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 575 key0).FastValid geometry rowPose659 := by decide +kernel
theorem row659_illegal : ¬ geometry.LegalContact rowPose659 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row659_reject_checked)
theorem row659_classified : RowClassified 659 := by
  intro p generated legal
  have he : rowPose659 = p := Option.some.inj (row659_generated.symm.trans generated)
  subst p
  exact (row659_illegal legal).elim

def rowPose660 : Pose 7 := ⟨perm21, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row660_fields : pairFieldsMatchB 188160 facet0 facet576 key0 key660 rowPose660 = true := by decide +kernel
theorem row660_generated : rootPair 660 = some rowPose660 :=
  pairFieldsMatchB_sound (by decide) row660_fields
theorem row660_source : sourceKey 660 ∈ geometry.profile (sourceOwner 660) := by decide +kernel
theorem row660_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 576 key0).FastValid geometry rowPose660 := by decide +kernel
theorem row660_illegal : ¬ geometry.LegalContact rowPose660 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row660_reject_checked)
theorem row660_classified : RowClassified 660 := by
  intro p generated legal
  have he : rowPose660 = p := Option.some.inj (row660_generated.symm.trans generated)
  subst p
  exact (row660_illegal legal).elim

def rowPose661 : Pose 7 := ⟨perm42, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row661_fields : pairFieldsMatchB 188160 facet0 facet577 key0 key661 rowPose661 = true := by decide +kernel
theorem row661_generated : rootPair 661 = some rowPose661 :=
  pairFieldsMatchB_sound (by decide) row661_fields
theorem row661_source : sourceKey 661 ∈ geometry.profile (sourceOwner 661) := by decide +kernel
theorem row661_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 577 key0).FastValid geometry rowPose661 := by decide +kernel
theorem row661_illegal : ¬ geometry.LegalContact rowPose661 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row661_reject_checked)
theorem row661_classified : RowClassified 661 := by
  intro p generated legal
  have he : rowPose661 = p := Option.some.inj (row661_generated.symm.trans generated)
  subst p
  exact (row661_illegal legal).elim

def rowPose662 : Pose 7 := ⟨perm55, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row662_fields : pairFieldsMatchB 188160 facet0 facet578 key0 key662 rowPose662 = true := by decide +kernel
theorem row662_generated : rootPair 662 = some rowPose662 :=
  pairFieldsMatchB_sound (by decide) row662_fields
theorem row662_source : sourceKey 662 ∈ geometry.profile (sourceOwner 662) := by decide +kernel
theorem row662_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 578 key1).FastValid geometry rowPose662 := by decide +kernel
theorem row662_illegal : ¬ geometry.LegalContact rowPose662 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row662_reject_checked)
theorem row662_classified : RowClassified 662 := by
  intro p generated legal
  have he : rowPose662 = p := Option.some.inj (row662_generated.symm.trans generated)
  subst p
  exact (row662_illegal legal).elim

def rowPose663 : Pose 7 := ⟨perm73, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 2, 0]⟩
theorem row663_fields : pairFieldsMatchB 188160 facet0 facet579 key0 key663 rowPose663 = true := by decide +kernel
theorem row663_generated : rootPair 663 = some rowPose663 :=
  pairFieldsMatchB_sound (by decide) row663_fields
theorem row663_source : sourceKey 663 ∈ geometry.profile (sourceOwner 663) := by decide +kernel
theorem row663_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 579 key0).FastValid geometry rowPose663 := by decide +kernel
theorem row663_illegal : ¬ geometry.LegalContact rowPose663 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row663_reject_checked)
theorem row663_classified : RowClassified 663 := by
  intro p generated legal
  have he : rowPose663 = p := Option.some.inj (row663_generated.symm.trans generated)
  subst p
  exact (row663_illegal legal).elim

def rowPose664 : Pose 7 := ⟨perm87, ![false, true, false, true, false, false, true], ![-2, 1, 0, 2, 0, -1, 1]⟩
theorem row664_fields : pairFieldsMatchB 188160 facet0 facet580 key0 key664 rowPose664 = true := by decide +kernel
theorem row664_generated : rootPair 664 = some rowPose664 :=
  pairFieldsMatchB_sound (by decide) row664_fields
theorem row664_source : sourceKey 664 ∈ geometry.profile (sourceOwner 664) := by decide +kernel
theorem row664_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 580 key1).FastValid geometry rowPose664 := by decide +kernel
theorem row664_illegal : ¬ geometry.LegalContact rowPose664 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row664_reject_checked)
theorem row664_classified : RowClassified 664 := by
  intro p generated legal
  have he : rowPose664 = p := Option.some.inj (row664_generated.symm.trans generated)
  subst p
  exact (row664_illegal legal).elim

def rowPose665 : Pose 7 := ⟨perm96, ![true, false, false, true, true, true, false], ![0, -1, 0, 2, 1, 1, -1]⟩
theorem row665_fields : pairFieldsMatchB 188160 facet0 facet581 key0 key665 rowPose665 = true := by decide +kernel
theorem row665_generated : rootPair 665 = some rowPose665 :=
  pairFieldsMatchB_sound (by decide) row665_fields
theorem row665_source : sourceKey 665 ∈ geometry.profile (sourceOwner 665) := by decide +kernel
theorem row665_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 581 key1).FastValid geometry rowPose665 := by decide +kernel
theorem row665_illegal : ¬ geometry.LegalContact rowPose665 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row665_reject_checked)
theorem row665_classified : RowClassified 665 := by
  intro p generated legal
  have he : rowPose665 = p := Option.some.inj (row665_generated.symm.trans generated)
  subst p
  exact (row665_illegal legal).elim

def rowPose666 : Pose 7 := ⟨perm0, ![false, true, true, false, false, false, false], ![-2, 1, 2, 0, 0, -1, -1]⟩
theorem row666_fields : pairFieldsMatchB 188160 facet0 facet582 key0 key666 rowPose666 = true := by decide +kernel
theorem row666_generated : rootPair 666 = some rowPose666 :=
  pairFieldsMatchB_sound (by decide) row666_fields
theorem row666_source : sourceKey 666 ∈ geometry.profile (sourceOwner 666) := by decide +kernel
theorem row666_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 582 key1).FastValid geometry rowPose666 := by decide +kernel
theorem row666_illegal : ¬ geometry.LegalContact rowPose666 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row666_reject_checked)
theorem row666_classified : RowClassified 666 := by
  intro p generated legal
  have he : rowPose666 = p := Option.some.inj (row666_generated.symm.trans generated)
  subst p
  exact (row666_illegal legal).elim

def rowPose667 : Pose 7 := ⟨perm16, ![true, false, true, false, true, true, true], ![0, -1, 2, 0, 1, 2, 2]⟩
theorem row667_fields : pairFieldsMatchB 188160 facet0 facet583 key0 key667 rowPose667 = true := by decide +kernel
theorem row667_generated : rootPair 667 = some rowPose667 :=
  pairFieldsMatchB_sound (by decide) row667_fields
theorem row667_source : sourceKey 667 ∈ geometry.profile (sourceOwner 667) := by decide +kernel
theorem row667_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 583 key0).FastValid geometry rowPose667 := by decide +kernel
theorem row667_illegal : ¬ geometry.LegalContact rowPose667 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row667_reject_checked)
theorem row667_classified : RowClassified 667 := by
  intro p generated legal
  have he : rowPose667 = p := Option.some.inj (row667_generated.symm.trans generated)
  subst p
  exact (row667_illegal legal).elim

def rowPose668 : Pose 7 := ⟨perm40, ![false, true, false, true, false, true, false], ![-2, 1, 0, 2, -1, 2, 0]⟩
theorem row668_fields : pairFieldsMatchB 188160 facet0 facet584 key0 key668 rowPose668 = true := by decide +kernel
theorem row668_generated : rootPair 668 = some rowPose668 :=
  pairFieldsMatchB_sound (by decide) row668_fields
theorem row668_source : sourceKey 668 ∈ geometry.profile (sourceOwner 668) := by decide +kernel
theorem row668_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 584 key1).FastValid geometry rowPose668 := by decide +kernel
theorem row668_illegal : ¬ geometry.LegalContact rowPose668 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row668_reject_checked)
theorem row668_classified : RowClassified 668 := by
  intro p generated legal
  have he : rowPose668 = p := Option.some.inj (row668_generated.symm.trans generated)
  subst p
  exact (row668_illegal legal).elim

def rowPose669 : Pose 7 := ⟨perm53, ![true, false, false, true, true, false, true], ![0, -1, 0, 2, 2, -1, 1]⟩
theorem row669_fields : pairFieldsMatchB 188160 facet0 facet585 key0 key669 rowPose669 = true := by decide +kernel
theorem row669_generated : rootPair 669 = some rowPose669 :=
  pairFieldsMatchB_sound (by decide) row669_fields
theorem row669_source : sourceKey 669 ∈ geometry.profile (sourceOwner 669) := by decide +kernel
theorem row669_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 585 key0).FastValid geometry rowPose669 := by decide +kernel
theorem row669_illegal : ¬ geometry.LegalContact rowPose669 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row669_reject_checked)
theorem row669_classified : RowClassified 669 := by
  intro p generated legal
  have he : rowPose669 = p := Option.some.inj (row669_generated.symm.trans generated)
  subst p
  exact (row669_illegal legal).elim

def rowPose670 : Pose 7 := ⟨perm74, ![true, false, true, true, true, false, true], ![0, -1, 2, 2, 1, -1, 1]⟩
theorem row670_fields : pairFieldsMatchB 188160 facet0 facet586 key0 key670 rowPose670 = true := by decide +kernel
theorem row670_generated : rootPair 670 = some rowPose670 :=
  pairFieldsMatchB_sound (by decide) row670_fields
theorem row670_source : sourceKey 670 ∈ geometry.profile (sourceOwner 670) := by decide +kernel
theorem row670_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 586 key0).FastValid geometry rowPose670 := by decide +kernel
theorem row670_illegal : ¬ geometry.LegalContact rowPose670 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row670_reject_checked)
theorem row670_classified : RowClassified 670 := by
  intro p generated legal
  have he : rowPose670 = p := Option.some.inj (row670_generated.symm.trans generated)
  subst p
  exact (row670_illegal legal).elim

def rowPose671 : Pose 7 := ⟨perm90, ![false, true, true, false, true, false, false], ![-2, 2, 2, 0, 2, 0, 0]⟩
theorem row671_fields : pairFieldsMatchB 188160 facet0 facet587 key0 key671 rowPose671 = true := by decide +kernel
theorem row671_generated : rootPair 671 = some rowPose671 :=
  pairFieldsMatchB_sound (by decide) row671_fields
theorem row671_source : sourceKey 671 ∈ geometry.profile (sourceOwner 671) := by decide +kernel
theorem row671_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 587 key0).FastValid geometry rowPose671 := by decide +kernel
theorem row671_illegal : ¬ geometry.LegalContact rowPose671 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row671_reject_checked)
theorem row671_classified : RowClassified 671 := by
  intro p generated legal
  have he : rowPose671 = p := Option.some.inj (row671_generated.symm.trans generated)
  subst p
  exact (row671_illegal legal).elim

theorem chunk20_classified (i : Fin 32) : RowClassified ⟨640 + i.val, by omega⟩ := by
  fin_cases i
  · exact row640_classified
  · exact row641_classified
  · exact row642_classified
  · exact row643_classified
  · exact row644_classified
  · exact row645_classified
  · exact row646_classified
  · exact row647_classified
  · exact row648_classified
  · exact row649_classified
  · exact row650_classified
  · exact row651_classified
  · exact row652_classified
  · exact row653_classified
  · exact row654_classified
  · exact row655_classified
  · exact row656_classified
  · exact row657_classified
  · exact row658_classified
  · exact row659_classified
  · exact row660_classified
  · exact row661_classified
  · exact row662_classified
  · exact row663_classified
  · exact row664_classified
  · exact row665_classified
  · exact row666_classified
  · exact row667_classified
  · exact row668_classified
  · exact row669_classified
  · exact row670_classified
  · exact row671_classified

theorem chunk20_source (i : Fin 32) : sourceKey ⟨640 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨640 + i.val, by omega⟩) := by
  fin_cases i
  · exact row640_source
  · exact row641_source
  · exact row642_source
  · exact row643_source
  · exact row644_source
  · exact row645_source
  · exact row646_source
  · exact row647_source
  · exact row648_source
  · exact row649_source
  · exact row650_source
  · exact row651_source
  · exact row652_source
  · exact row653_source
  · exact row654_source
  · exact row655_source
  · exact row656_source
  · exact row657_source
  · exact row658_source
  · exact row659_source
  · exact row660_source
  · exact row661_source
  · exact row662_source
  · exact row663_source
  · exact row664_source
  · exact row665_source
  · exact row666_source
  · exact row667_source
  · exact row668_source
  · exact row669_source
  · exact row670_source
  · exact row671_source

#print axioms chunk20_classified
end SparseMonotiles.Contact.RootZeroPilot7
