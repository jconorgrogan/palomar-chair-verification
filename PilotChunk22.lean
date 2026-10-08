module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose704 : Pose 7 := ⟨perm89, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row704_fields : pairFieldsMatchB 188160 facet0 facet615 key0 key704 rowPose704 = true := by decide +kernel
theorem row704_generated : rootPair 704 = some rowPose704 :=
  pairFieldsMatchB_sound (by decide) row704_fields
theorem row704_source : sourceKey 704 ∈ geometry.profile (sourceOwner 704) := by decide +kernel
theorem row704_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 615 key1).FastValid geometry rowPose704 := by decide +kernel
theorem row704_illegal : ¬ geometry.LegalContact rowPose704 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row704_reject_checked)
theorem row704_classified : RowClassified 704 := by
  intro p generated legal
  have he : rowPose704 = p := Option.some.inj (row704_generated.symm.trans generated)
  subst p
  exact (row704_illegal legal).elim

def rowPose705 : Pose 7 := ⟨perm101, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row705_fields : pairFieldsMatchB 188160 facet0 facet616 key0 key705 rowPose705 = true := by decide +kernel
theorem row705_generated : rootPair 705 = some rowPose705 :=
  pairFieldsMatchB_sound (by decide) row705_fields
theorem row705_source : sourceKey 705 ∈ geometry.profile (sourceOwner 705) := by decide +kernel
theorem row705_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 616 key0).FastValid geometry rowPose705 := by decide +kernel
theorem row705_illegal : ¬ geometry.LegalContact rowPose705 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row705_reject_checked)
theorem row705_classified : RowClassified 705 := by
  intro p generated legal
  have he : rowPose705 = p := Option.some.inj (row705_generated.symm.trans generated)
  subst p
  exact (row705_illegal legal).elim

def rowPose706 : Pose 7 := ⟨perm10, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row706_fields : pairFieldsMatchB 188160 facet0 facet617 key0 key706 rowPose706 = true := by decide +kernel
theorem row706_generated : rootPair 706 = some rowPose706 :=
  pairFieldsMatchB_sound (by decide) row706_fields
theorem row706_source : sourceKey 706 ∈ geometry.profile (sourceOwner 706) := by decide +kernel
theorem row706_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 617 key1).FastValid geometry rowPose706 := by decide +kernel
theorem row706_illegal : ¬ geometry.LegalContact rowPose706 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row706_reject_checked)
theorem row706_classified : RowClassified 706 := by
  intro p generated legal
  have he : rowPose706 = p := Option.some.inj (row706_generated.symm.trans generated)
  subst p
  exact (row706_illegal legal).elim

def rowPose707 : Pose 7 := ⟨perm22, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row707_fields : pairFieldsMatchB 188160 facet0 facet618 key0 key707 rowPose707 = true := by decide +kernel
theorem row707_generated : rootPair 707 = some rowPose707 :=
  pairFieldsMatchB_sound (by decide) row707_fields
theorem row707_source : sourceKey 707 ∈ geometry.profile (sourceOwner 707) := by decide +kernel
theorem row707_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 618 key0).FastValid geometry rowPose707 := by decide +kernel
theorem row707_illegal : ¬ geometry.LegalContact rowPose707 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row707_reject_checked)
theorem row707_classified : RowClassified 707 := by
  intro p generated legal
  have he : rowPose707 = p := Option.some.inj (row707_generated.symm.trans generated)
  subst p
  exact (row707_illegal legal).elim

def rowPose708 : Pose 7 := ⟨perm37, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row708_fields : pairFieldsMatchB 188160 facet0 facet619 key0 key708 rowPose708 = true := by decide +kernel
theorem row708_generated : rootPair 708 = some rowPose708 :=
  pairFieldsMatchB_sound (by decide) row708_fields
theorem row708_source : sourceKey 708 ∈ geometry.profile (sourceOwner 708) := by decide +kernel
theorem row708_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 619 key1).FastValid geometry rowPose708 := by decide +kernel
theorem row708_illegal : ¬ geometry.LegalContact rowPose708 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row708_reject_checked)
theorem row708_classified : RowClassified 708 := by
  intro p generated legal
  have he : rowPose708 = p := Option.some.inj (row708_generated.symm.trans generated)
  subst p
  exact (row708_illegal legal).elim

def rowPose709 : Pose 7 := ⟨perm58, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row709_fields : pairFieldsMatchB 188160 facet0 facet620 key0 key709 rowPose709 = true := by decide +kernel
theorem row709_generated : rootPair 709 = some rowPose709 :=
  pairFieldsMatchB_sound (by decide) row709_fields
theorem row709_source : sourceKey 709 ∈ geometry.profile (sourceOwner 709) := by decide +kernel
theorem row709_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 620 key1).FastValid geometry rowPose709 := by decide +kernel
theorem row709_illegal : ¬ geometry.LegalContact rowPose709 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row709_reject_checked)
theorem row709_classified : RowClassified 709 := by
  intro p generated legal
  have he : rowPose709 = p := Option.some.inj (row709_generated.symm.trans generated)
  subst p
  exact (row709_illegal legal).elim

def rowPose710 : Pose 7 := ⟨perm74, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row710_fields : pairFieldsMatchB 188160 facet0 facet621 key0 key710 rowPose710 = true := by decide +kernel
theorem row710_generated : rootPair 710 = some rowPose710 :=
  pairFieldsMatchB_sound (by decide) row710_fields
theorem row710_source : sourceKey 710 ∈ geometry.profile (sourceOwner 710) := by decide +kernel
theorem row710_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 565 key8).FastValid geometry rowPose710 := by decide +kernel
theorem row710_illegal : ¬ geometry.LegalContact rowPose710 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row710_reject_checked)
theorem row710_classified : RowClassified 710 := by
  intro p generated legal
  have he : rowPose710 = p := Option.some.inj (row710_generated.symm.trans generated)
  subst p
  exact (row710_illegal legal).elim

def rowPose711 : Pose 7 := ⟨perm69, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row711_fields : pairFieldsMatchB 188160 facet0 facet621 key0 key711 rowPose711 = true := by decide +kernel
theorem row711_generated : rootPair 711 = some rowPose711 :=
  pairFieldsMatchB_sound (by decide) row711_fields
theorem row711_source : sourceKey 711 ∈ geometry.profile (sourceOwner 711) := by decide +kernel
theorem row711_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 621 key0).FastValid geometry rowPose711 := by decide +kernel
theorem row711_illegal : ¬ geometry.LegalContact rowPose711 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row711_reject_checked)
theorem row711_classified : RowClassified 711 := by
  intro p generated legal
  have he : rowPose711 = p := Option.some.inj (row711_generated.symm.trans generated)
  subst p
  exact (row711_illegal legal).elim

def rowPose712 : Pose 7 := ⟨perm87, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row712_fields : pairFieldsMatchB 188160 facet0 facet622 key0 key712 rowPose712 = true := by decide +kernel
theorem row712_generated : rootPair 712 = some rowPose712 :=
  pairFieldsMatchB_sound (by decide) row712_fields
theorem row712_source : sourceKey 712 ∈ geometry.profile (sourceOwner 712) := by decide +kernel
theorem row712_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 622 key0).FastValid geometry rowPose712 := by decide +kernel
theorem row712_illegal : ¬ geometry.LegalContact rowPose712 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row712_reject_checked)
theorem row712_classified : RowClassified 712 := by
  intro p generated legal
  have he : rowPose712 = p := Option.some.inj (row712_generated.symm.trans generated)
  subst p
  exact (row712_illegal legal).elim

def rowPose713 : Pose 7 := ⟨perm96, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row713_fields : pairFieldsMatchB 188160 facet0 facet623 key0 key713 rowPose713 = true := by decide +kernel
theorem row713_generated : rootPair 713 = some rowPose713 :=
  pairFieldsMatchB_sound (by decide) row713_fields
theorem row713_source : sourceKey 713 ∈ geometry.profile (sourceOwner 713) := by decide +kernel
theorem row713_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 623 key0).FastValid geometry rowPose713 := by decide +kernel
theorem row713_illegal : ¬ geometry.LegalContact rowPose713 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row713_reject_checked)
theorem row713_classified : RowClassified 713 := by
  intro p generated legal
  have he : rowPose713 = p := Option.some.inj (row713_generated.symm.trans generated)
  subst p
  exact (row713_illegal legal).elim

def rowPose714 : Pose 7 := ⟨perm0, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row714_fields : pairFieldsMatchB 188160 facet0 facet624 key0 key714 rowPose714 = true := by decide +kernel
theorem row714_generated : rootPair 714 = some rowPose714 :=
  pairFieldsMatchB_sound (by decide) row714_fields
theorem row714_source : sourceKey 714 ∈ geometry.profile (sourceOwner 714) := by decide +kernel
theorem row714_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 624 key0).FastValid geometry rowPose714 := by decide +kernel
theorem row714_illegal : ¬ geometry.LegalContact rowPose714 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row714_reject_checked)
theorem row714_classified : RowClassified 714 := by
  intro p generated legal
  have he : rowPose714 = p := Option.some.inj (row714_generated.symm.trans generated)
  subst p
  exact (row714_illegal legal).elim

def rowPose715 : Pose 7 := ⟨perm21, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row715_fields : pairFieldsMatchB 188160 facet0 facet625 key0 key715 rowPose715 = true := by decide +kernel
theorem row715_generated : rootPair 715 = some rowPose715 :=
  pairFieldsMatchB_sound (by decide) row715_fields
theorem row715_source : sourceKey 715 ∈ geometry.profile (sourceOwner 715) := by decide +kernel
theorem row715_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 513 key8).FastValid geometry rowPose715 := by decide +kernel
theorem row715_illegal : ¬ geometry.LegalContact rowPose715 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row715_reject_checked)
theorem row715_classified : RowClassified 715 := by
  intro p generated legal
  have he : rowPose715 = p := Option.some.inj (row715_generated.symm.trans generated)
  subst p
  exact (row715_illegal legal).elim

def rowPose716 : Pose 7 := ⟨perm24, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row716_fields : pairFieldsMatchB 188160 facet0 facet625 key0 key716 rowPose716 = true := by decide +kernel
theorem row716_generated : rootPair 716 = some rowPose716 :=
  pairFieldsMatchB_sound (by decide) row716_fields
theorem row716_source : sourceKey 716 ∈ geometry.profile (sourceOwner 716) := by decide +kernel
theorem row716_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 625 key0).FastValid geometry rowPose716 := by decide +kernel
theorem row716_illegal : ¬ geometry.LegalContact rowPose716 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row716_reject_checked)
theorem row716_classified : RowClassified 716 := by
  intro p generated legal
  have he : rowPose716 = p := Option.some.inj (row716_generated.symm.trans generated)
  subst p
  exact (row716_illegal legal).elim

def rowPose717 : Pose 7 := ⟨perm37, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row717_fields : pairFieldsMatchB 188160 facet0 facet626 key0 key717 rowPose717 = true := by decide +kernel
theorem row717_generated : rootPair 717 = some rowPose717 :=
  pairFieldsMatchB_sound (by decide) row717_fields
theorem row717_source : sourceKey 717 ∈ geometry.profile (sourceOwner 717) := by decide +kernel
theorem row717_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 626 key1).FastValid geometry rowPose717 := by decide +kernel
theorem row717_illegal : ¬ geometry.LegalContact rowPose717 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row717_reject_checked)
theorem row717_classified : RowClassified 717 := by
  intro p generated legal
  have he : rowPose717 = p := Option.some.inj (row717_generated.symm.trans generated)
  subst p
  exact (row717_illegal legal).elim

def rowPose718 : Pose 7 := ⟨perm58, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row718_fields : pairFieldsMatchB 188160 facet0 facet627 key0 key718 rowPose718 = true := by decide +kernel
theorem row718_generated : rootPair 718 = some rowPose718 :=
  pairFieldsMatchB_sound (by decide) row718_fields
theorem row718_source : sourceKey 718 ∈ geometry.profile (sourceOwner 718) := by decide +kernel
theorem row718_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 627 key1).FastValid geometry rowPose718 := by decide +kernel
theorem row718_illegal : ¬ geometry.LegalContact rowPose718 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row718_reject_checked)
theorem row718_classified : RowClassified 718 := by
  intro p generated legal
  have he : rowPose718 = p := Option.some.inj (row718_generated.symm.trans generated)
  subst p
  exact (row718_illegal legal).elim

def rowPose719 : Pose 7 := ⟨perm71, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row719_fields : pairFieldsMatchB 188160 facet0 facet628 key0 key719 rowPose719 = true := by decide +kernel
theorem row719_generated : rootPair 719 = some rowPose719 :=
  pairFieldsMatchB_sound (by decide) row719_fields
theorem row719_source : sourceKey 719 ∈ geometry.profile (sourceOwner 719) := by decide +kernel
theorem row719_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 628 key0).FastValid geometry rowPose719 := by decide +kernel
theorem row719_illegal : ¬ geometry.LegalContact rowPose719 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row719_reject_checked)
theorem row719_classified : RowClassified 719 := by
  intro p generated legal
  have he : rowPose719 = p := Option.some.inj (row719_generated.symm.trans generated)
  subst p
  exact (row719_illegal legal).elim

def rowPose720 : Pose 7 := ⟨perm95, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row720_fields : pairFieldsMatchB 188160 facet0 facet629 key0 key720 rowPose720 = true := by decide +kernel
theorem row720_generated : rootPair 720 = some rowPose720 :=
  pairFieldsMatchB_sound (by decide) row720_fields
theorem row720_source : sourceKey 720 ∈ geometry.profile (sourceOwner 720) := by decide +kernel
theorem row720_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 629 key1).FastValid geometry rowPose720 := by decide +kernel
theorem row720_illegal : ¬ geometry.LegalContact rowPose720 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row720_reject_checked)
theorem row720_classified : RowClassified 720 := by
  intro p generated legal
  have he : rowPose720 = p := Option.some.inj (row720_generated.symm.trans generated)
  subst p
  exact (row720_illegal legal).elim

def rowPose721 : Pose 7 := ⟨perm111, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row721_fields : pairFieldsMatchB 188160 facet0 facet630 key0 key721 rowPose721 = true := by decide +kernel
theorem row721_generated : rootPair 721 = some rowPose721 :=
  pairFieldsMatchB_sound (by decide) row721_fields
theorem row721_source : sourceKey 721 ∈ geometry.profile (sourceOwner 721) := by decide +kernel
theorem row721_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 630 key0).FastValid geometry rowPose721 := by decide +kernel
theorem row721_illegal : ¬ geometry.LegalContact rowPose721 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row721_reject_checked)
theorem row721_classified : RowClassified 721 := by
  intro p generated legal
  have he : rowPose721 = p := Option.some.inj (row721_generated.symm.trans generated)
  subst p
  exact (row721_illegal legal).elim

def rowPose722 : Pose 7 := ⟨perm15, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row722_fields : pairFieldsMatchB 188160 facet0 facet631 key0 key722 rowPose722 = true := by decide +kernel
theorem row722_generated : rootPair 722 = some rowPose722 :=
  pairFieldsMatchB_sound (by decide) row722_fields
theorem row722_source : sourceKey 722 ∈ geometry.profile (sourceOwner 722) := by decide +kernel
theorem row722_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 631 key1).FastValid geometry rowPose722 := by decide +kernel
theorem row722_illegal : ¬ geometry.LegalContact rowPose722 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row722_reject_checked)
theorem row722_classified : RowClassified 722 := by
  intro p generated legal
  have he : rowPose722 = p := Option.some.inj (row722_generated.symm.trans generated)
  subst p
  exact (row722_illegal legal).elim

def rowPose723 : Pose 7 := ⟨perm24, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row723_fields : pairFieldsMatchB 188160 facet0 facet632 key0 key723 rowPose723 = true := by decide +kernel
theorem row723_generated : rootPair 723 = some rowPose723 :=
  pairFieldsMatchB_sound (by decide) row723_fields
theorem row723_source : sourceKey 723 ∈ geometry.profile (sourceOwner 723) := by decide +kernel
theorem row723_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 632 key1).FastValid geometry rowPose723 := by decide +kernel
theorem row723_illegal : ¬ geometry.LegalContact rowPose723 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row723_reject_checked)
theorem row723_classified : RowClassified 723 := by
  intro p generated legal
  have he : rowPose723 = p := Option.some.inj (row723_generated.symm.trans generated)
  subst p
  exact (row723_illegal legal).elim

def rowPose724 : Pose 7 := ⟨perm38, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row724_fields : pairFieldsMatchB 188160 facet0 facet633 key0 key724 rowPose724 = true := by decide +kernel
theorem row724_generated : rootPair 724 = some rowPose724 :=
  pairFieldsMatchB_sound (by decide) row724_fields
theorem row724_source : sourceKey 724 ∈ geometry.profile (sourceOwner 724) := by decide +kernel
theorem row724_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 633 key0).FastValid geometry rowPose724 := by decide +kernel
theorem row724_illegal : ¬ geometry.LegalContact rowPose724 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row724_reject_checked)
theorem row724_classified : RowClassified 724 := by
  intro p generated legal
  have he : rowPose724 = p := Option.some.inj (row724_generated.symm.trans generated)
  subst p
  exact (row724_illegal legal).elim

def rowPose725 : Pose 7 := ⟨perm56, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, 0, 2]⟩
theorem row725_fields : pairFieldsMatchB 188160 facet0 facet634 key0 key725 rowPose725 = true := by decide +kernel
theorem row725_generated : rootPair 725 = some rowPose725 :=
  pairFieldsMatchB_sound (by decide) row725_fields
theorem row725_source : sourceKey 725 ∈ geometry.profile (sourceOwner 725) := by decide +kernel
theorem row725_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 634 key1).FastValid geometry rowPose725 := by decide +kernel
theorem row725_illegal : ¬ geometry.LegalContact rowPose725 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row725_reject_checked)
theorem row725_classified : RowClassified 725 := by
  intro p generated legal
  have he : rowPose725 = p := Option.some.inj (row725_generated.symm.trans generated)
  subst p
  exact (row725_illegal legal).elim

def rowPose726 : Pose 7 := ⟨perm69, ![true, false, true, false, true, true, false], ![0, -1, 2, 0, 2, 1, -1]⟩
theorem row726_fields : pairFieldsMatchB 188160 facet0 facet635 key0 key726 rowPose726 = true := by decide +kernel
theorem row726_generated : rootPair 726 = some rowPose726 :=
  pairFieldsMatchB_sound (by decide) row726_fields
theorem row726_source : sourceKey 726 ∈ geometry.profile (sourceOwner 726) := by decide +kernel
theorem row726_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 635 key0).FastValid geometry rowPose726 := by decide +kernel
theorem row726_illegal : ¬ geometry.LegalContact rowPose726 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row726_reject_checked)
theorem row726_classified : RowClassified 726 := by
  intro p generated legal
  have he : rowPose726 = p := Option.some.inj (row726_generated.symm.trans generated)
  subst p
  exact (row726_illegal legal).elim

def rowPose727 : Pose 7 := ⟨perm90, ![false, true, true, false, false, false, true], ![-2, 1, 2, 0, -1, -1, 1]⟩
theorem row727_fields : pairFieldsMatchB 188160 facet0 facet636 key0 key727 rowPose727 = true := by decide +kernel
theorem row727_generated : rootPair 727 = some rowPose727 :=
  pairFieldsMatchB_sound (by decide) row727_fields
theorem row727_source : sourceKey 727 ∈ geometry.profile (sourceOwner 727) := by decide +kernel
theorem row727_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 636 key0).FastValid geometry rowPose727 := by decide +kernel
theorem row727_illegal : ¬ geometry.LegalContact rowPose727 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row727_reject_checked)
theorem row727_classified : RowClassified 727 := by
  intro p generated legal
  have he : rowPose727 = p := Option.some.inj (row727_generated.symm.trans generated)
  subst p
  exact (row727_illegal legal).elim

def rowPose728 : Pose 7 := ⟨perm96, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row728_fields : pairFieldsMatchB 188160 facet0 facet637 key0 key728 rowPose728 = true := by decide +kernel
theorem row728_generated : rootPair 728 = some rowPose728 :=
  pairFieldsMatchB_sound (by decide) row728_fields
theorem row728_source : sourceKey 728 ∈ geometry.profile (sourceOwner 728) := by decide +kernel
theorem row728_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 637 key0).FastValid geometry rowPose728 := by decide +kernel
theorem row728_illegal : ¬ geometry.LegalContact rowPose728 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row728_reject_checked)
theorem row728_classified : RowClassified 728 := by
  intro p generated legal
  have he : rowPose728 = p := Option.some.inj (row728_generated.symm.trans generated)
  subst p
  exact (row728_illegal legal).elim

def rowPose729 : Pose 7 := ⟨perm111, ![true, true, false, true, true, false, true], ![0, 2, 0, 2, 2, 0, 2]⟩
theorem row729_fields : pairFieldsMatchB 188160 facet0 facet637 key0 key729 rowPose729 = true := by decide +kernel
theorem row729_generated : rootPair 729 = some rowPose729 :=
  pairFieldsMatchB_sound (by decide) row729_fields
theorem row729_source : sourceKey 729 ∈ geometry.profile (sourceOwner 729) := by decide +kernel
theorem row729_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 188 key8).FastValid geometry rowPose729 := by decide +kernel
theorem row729_illegal : ¬ geometry.LegalContact rowPose729 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row729_reject_checked)
theorem row729_classified : RowClassified 729 := by
  intro p generated legal
  have he : rowPose729 = p := Option.some.inj (row729_generated.symm.trans generated)
  subst p
  exact (row729_illegal legal).elim

def rowPose730 : Pose 7 := ⟨perm15, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row730_fields : pairFieldsMatchB 188160 facet0 facet638 key0 key730 rowPose730 = true := by decide +kernel
theorem row730_generated : rootPair 730 = some rowPose730 :=
  pairFieldsMatchB_sound (by decide) row730_fields
theorem row730_source : sourceKey 730 ∈ geometry.profile (sourceOwner 730) := by decide +kernel
theorem row730_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 638 key0).FastValid geometry rowPose730 := by decide +kernel
theorem row730_illegal : ¬ geometry.LegalContact rowPose730 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row730_reject_checked)
theorem row730_classified : RowClassified 730 := by
  intro p generated legal
  have he : rowPose730 = p := Option.some.inj (row730_generated.symm.trans generated)
  subst p
  exact (row730_illegal legal).elim

def rowPose731 : Pose 7 := ⟨perm24, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row731_fields : pairFieldsMatchB 188160 facet0 facet639 key0 key731 rowPose731 = true := by decide +kernel
theorem row731_generated : rootPair 731 = some rowPose731 :=
  pairFieldsMatchB_sound (by decide) row731_fields
theorem row731_source : sourceKey 731 ∈ geometry.profile (sourceOwner 731) := by decide +kernel
theorem row731_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 639 key0).FastValid geometry rowPose731 := by decide +kernel
theorem row731_illegal : ¬ geometry.LegalContact rowPose731 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row731_reject_checked)
theorem row731_classified : RowClassified 731 := by
  intro p generated legal
  have he : rowPose731 = p := Option.some.inj (row731_generated.symm.trans generated)
  subst p
  exact (row731_illegal legal).elim

def rowPose732 : Pose 7 := ⟨perm38, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row732_fields : pairFieldsMatchB 188160 facet0 facet640 key0 key732 rowPose732 = true := by decide +kernel
theorem row732_generated : rootPair 732 = some rowPose732 :=
  pairFieldsMatchB_sound (by decide) row732_fields
theorem row732_source : sourceKey 732 ∈ geometry.profile (sourceOwner 732) := by decide +kernel
theorem row732_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 640 key1).FastValid geometry rowPose732 := by decide +kernel
theorem row732_illegal : ¬ geometry.LegalContact rowPose732 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row732_reject_checked)
theorem row732_classified : RowClassified 732 := by
  intro p generated legal
  have he : rowPose732 = p := Option.some.inj (row732_generated.symm.trans generated)
  subst p
  exact (row732_illegal legal).elim

def rowPose733 : Pose 7 := ⟨perm56, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row733_fields : pairFieldsMatchB 188160 facet0 facet641 key0 key733 rowPose733 = true := by decide +kernel
theorem row733_generated : rootPair 733 = some rowPose733 :=
  pairFieldsMatchB_sound (by decide) row733_fields
theorem row733_source : sourceKey 733 ∈ geometry.profile (sourceOwner 733) := by decide +kernel
theorem row733_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 641 key0).FastValid geometry rowPose733 := by decide +kernel
theorem row733_illegal : ¬ geometry.LegalContact rowPose733 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row733_reject_checked)
theorem row733_classified : RowClassified 733 := by
  intro p generated legal
  have he : rowPose733 = p := Option.some.inj (row733_generated.symm.trans generated)
  subst p
  exact (row733_illegal legal).elim

def rowPose734 : Pose 7 := ⟨perm69, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row734_fields : pairFieldsMatchB 188160 facet0 facet642 key0 key734 rowPose734 = true := by decide +kernel
theorem row734_generated : rootPair 734 = some rowPose734 :=
  pairFieldsMatchB_sound (by decide) row734_fields
theorem row734_source : sourceKey 734 ∈ geometry.profile (sourceOwner 734) := by decide +kernel
theorem row734_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 642 key1).FastValid geometry rowPose734 := by decide +kernel
theorem row734_illegal : ¬ geometry.LegalContact rowPose734 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row734_reject_checked)
theorem row734_classified : RowClassified 734 := by
  intro p generated legal
  have he : rowPose734 = p := Option.some.inj (row734_generated.symm.trans generated)
  subst p
  exact (row734_illegal legal).elim

def rowPose735 : Pose 7 := ⟨perm90, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row735_fields : pairFieldsMatchB 188160 facet0 facet643 key0 key735 rowPose735 = true := by decide +kernel
theorem row735_generated : rootPair 735 = some rowPose735 :=
  pairFieldsMatchB_sound (by decide) row735_fields
theorem row735_source : sourceKey 735 ∈ geometry.profile (sourceOwner 735) := by decide +kernel
theorem row735_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 643 key1).FastValid geometry rowPose735 := by decide +kernel
theorem row735_illegal : ¬ geometry.LegalContact rowPose735 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row735_reject_checked)
theorem row735_classified : RowClassified 735 := by
  intro p generated legal
  have he : rowPose735 = p := Option.some.inj (row735_generated.symm.trans generated)
  subst p
  exact (row735_illegal legal).elim

theorem chunk22_classified (i : Fin 32) : RowClassified ⟨704 + i.val, by omega⟩ := by
  fin_cases i
  · exact row704_classified
  · exact row705_classified
  · exact row706_classified
  · exact row707_classified
  · exact row708_classified
  · exact row709_classified
  · exact row710_classified
  · exact row711_classified
  · exact row712_classified
  · exact row713_classified
  · exact row714_classified
  · exact row715_classified
  · exact row716_classified
  · exact row717_classified
  · exact row718_classified
  · exact row719_classified
  · exact row720_classified
  · exact row721_classified
  · exact row722_classified
  · exact row723_classified
  · exact row724_classified
  · exact row725_classified
  · exact row726_classified
  · exact row727_classified
  · exact row728_classified
  · exact row729_classified
  · exact row730_classified
  · exact row731_classified
  · exact row732_classified
  · exact row733_classified
  · exact row734_classified
  · exact row735_classified

theorem chunk22_source (i : Fin 32) : sourceKey ⟨704 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨704 + i.val, by omega⟩) := by
  fin_cases i
  · exact row704_source
  · exact row705_source
  · exact row706_source
  · exact row707_source
  · exact row708_source
  · exact row709_source
  · exact row710_source
  · exact row711_source
  · exact row712_source
  · exact row713_source
  · exact row714_source
  · exact row715_source
  · exact row716_source
  · exact row717_source
  · exact row718_source
  · exact row719_source
  · exact row720_source
  · exact row721_source
  · exact row722_source
  · exact row723_source
  · exact row724_source
  · exact row725_source
  · exact row726_source
  · exact row727_source
  · exact row728_source
  · exact row729_source
  · exact row730_source
  · exact row731_source
  · exact row732_source
  · exact row733_source
  · exact row734_source
  · exact row735_source

#print axioms chunk22_classified
end SparseMonotiles.Contact.RootZeroPilot7
