module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose864 : Pose 7 := ⟨perm69, ![true, false, false, true, false, false, false], ![0, -1, 0, 2, -1, -1, -1]⟩
theorem row864_fields : pairFieldsMatchB 188160 facet0 facet755 key0 key864 rowPose864 = true := by decide +kernel
theorem row864_generated : rootPair 864 = some rowPose864 :=
  pairFieldsMatchB_sound (by decide) row864_fields
theorem row864_source : sourceKey 864 ∈ geometry.profile (sourceOwner 864) := by decide +kernel
theorem row864_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 755 key0).FastValid geometry rowPose864 := by decide +kernel
theorem row864_illegal : ¬ geometry.LegalContact rowPose864 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row864_reject_checked)
theorem row864_classified : RowClassified 864 := by
  intro p generated legal
  have he : rowPose864 = p := Option.some.inj (row864_generated.symm.trans generated)
  subst p
  exact (row864_illegal legal).elim

def rowPose865 : Pose 7 := ⟨perm90, ![false, false, true, true, false, false, true], ![-2, -1, 2, 2, 0, -1, 1]⟩
theorem row865_fields : pairFieldsMatchB 188160 facet0 facet756 key0 key865 rowPose865 = true := by decide +kernel
theorem row865_generated : rootPair 865 = some rowPose865 :=
  pairFieldsMatchB_sound (by decide) row865_fields
theorem row865_source : sourceKey 865 ∈ geometry.profile (sourceOwner 865) := by decide +kernel
theorem row865_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 756 key0).FastValid geometry rowPose865 := by decide +kernel
theorem row865_illegal : ¬ geometry.LegalContact rowPose865 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row865_reject_checked)
theorem row865_classified : RowClassified 865 := by
  intro p generated legal
  have he : rowPose865 = p := Option.some.inj (row865_generated.symm.trans generated)
  subst p
  exact (row865_illegal legal).elim

def rowPose866 : Pose 7 := ⟨perm106, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 1, 2, 0]⟩
theorem row866_fields : pairFieldsMatchB 188160 facet0 facet757 key0 key866 rowPose866 = true := by decide +kernel
theorem row866_generated : rootPair 866 = some rowPose866 :=
  pairFieldsMatchB_sound (by decide) row866_fields
theorem row866_source : sourceKey 866 ∈ geometry.profile (sourceOwner 866) := by decide +kernel
theorem row866_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 757 key1).FastValid geometry rowPose866 := by decide +kernel
theorem row866_illegal : ¬ geometry.LegalContact rowPose866 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row866_reject_checked)
theorem row866_classified : RowClassified 866 := by
  intro p generated legal
  have he : rowPose866 = p := Option.some.inj (row866_generated.symm.trans generated)
  subst p
  exact (row866_illegal legal).elim

def rowPose867 : Pose 7 := ⟨perm15, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row867_fields : pairFieldsMatchB 188160 facet0 facet758 key0 key867 rowPose867 = true := by decide +kernel
theorem row867_generated : rootPair 867 = some rowPose867 :=
  pairFieldsMatchB_sound (by decide) row867_fields
theorem row867_source : sourceKey 867 ∈ geometry.profile (sourceOwner 867) := by decide +kernel
theorem row867_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 758 key0).FastValid geometry rowPose867 := by decide +kernel
theorem row867_illegal : ¬ geometry.LegalContact rowPose867 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row867_reject_checked)
theorem row867_classified : RowClassified 867 := by
  intro p generated legal
  have he : rowPose867 = p := Option.some.inj (row867_generated.symm.trans generated)
  subst p
  exact (row867_illegal legal).elim

def rowPose868 : Pose 7 := ⟨perm24, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row868_fields : pairFieldsMatchB 188160 facet0 facet759 key0 key868 rowPose868 = true := by decide +kernel
theorem row868_generated : rootPair 868 = some rowPose868 :=
  pairFieldsMatchB_sound (by decide) row868_fields
theorem row868_source : sourceKey 868 ∈ geometry.profile (sourceOwner 868) := by decide +kernel
theorem row868_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 759 key0).FastValid geometry rowPose868 := by decide +kernel
theorem row868_illegal : ¬ geometry.LegalContact rowPose868 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row868_reject_checked)
theorem row868_classified : RowClassified 868 := by
  intro p generated legal
  have he : rowPose868 = p := Option.some.inj (row868_generated.symm.trans generated)
  subst p
  exact (row868_illegal legal).elim

def rowPose869 : Pose 7 := ⟨perm37, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row869_fields : pairFieldsMatchB 188160 facet0 facet760 key0 key869 rowPose869 = true := by decide +kernel
theorem row869_generated : rootPair 869 = some rowPose869 :=
  pairFieldsMatchB_sound (by decide) row869_fields
theorem row869_source : sourceKey 869 ∈ geometry.profile (sourceOwner 869) := by decide +kernel
theorem row869_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 704 key8).FastValid geometry rowPose869 := by decide +kernel
theorem row869_illegal : ¬ geometry.LegalContact rowPose869 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row869_reject_checked)
theorem row869_classified : RowClassified 869 := by
  intro p generated legal
  have he : rowPose869 = p := Option.some.inj (row869_generated.symm.trans generated)
  subst p
  exact (row869_illegal legal).elim

def rowPose870 : Pose 7 := ⟨perm42, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row870_fields : pairFieldsMatchB 188160 facet0 facet760 key0 key870 rowPose870 = true := by decide +kernel
theorem row870_generated : rootPair 870 = some rowPose870 :=
  pairFieldsMatchB_sound (by decide) row870_fields
theorem row870_source : sourceKey 870 ∈ geometry.profile (sourceOwner 870) := by decide +kernel
theorem row870_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 760 key0).FastValid geometry rowPose870 := by decide +kernel
theorem row870_illegal : ¬ geometry.LegalContact rowPose870 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row870_reject_checked)
theorem row870_classified : RowClassified 870 := by
  intro p generated legal
  have he : rowPose870 = p := Option.some.inj (row870_generated.symm.trans generated)
  subst p
  exact (row870_illegal legal).elim

def rowPose871 : Pose 7 := ⟨perm53, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row871_fields : pairFieldsMatchB 188160 facet0 facet761 key0 key871 rowPose871 = true := by decide +kernel
theorem row871_generated : rootPair 871 = some rowPose871 :=
  pairFieldsMatchB_sound (by decide) row871_fields
theorem row871_source : sourceKey 871 ∈ geometry.profile (sourceOwner 871) := by decide +kernel
theorem row871_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 761 key1).FastValid geometry rowPose871 := by decide +kernel
theorem row871_illegal : ¬ geometry.LegalContact rowPose871 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row871_reject_checked)
theorem row871_classified : RowClassified 871 := by
  intro p generated legal
  have he : rowPose871 = p := Option.some.inj (row871_generated.symm.trans generated)
  subst p
  exact (row871_illegal legal).elim

def rowPose872 : Pose 7 := ⟨perm74, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row872_fields : pairFieldsMatchB 188160 facet0 facet762 key0 key872 rowPose872 = true := by decide +kernel
theorem row872_generated : rootPair 872 = some rowPose872 :=
  pairFieldsMatchB_sound (by decide) row872_fields
theorem row872_source : sourceKey 872 ∈ geometry.profile (sourceOwner 872) := by decide +kernel
theorem row872_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 762 key1).FastValid geometry rowPose872 := by decide +kernel
theorem row872_illegal : ¬ geometry.LegalContact rowPose872 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row872_reject_checked)
theorem row872_classified : RowClassified 872 := by
  intro p generated legal
  have he : rowPose872 = p := Option.some.inj (row872_generated.symm.trans generated)
  subst p
  exact (row872_illegal legal).elim

def rowPose873 : Pose 7 := ⟨perm89, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row873_fields : pairFieldsMatchB 188160 facet0 facet763 key0 key873 rowPose873 = true := by decide +kernel
theorem row873_generated : rootPair 873 = some rowPose873 :=
  pairFieldsMatchB_sound (by decide) row873_fields
theorem row873_source : sourceKey 873 ∈ geometry.profile (sourceOwner 873) := by decide +kernel
theorem row873_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 763 key0).FastValid geometry rowPose873 := by decide +kernel
theorem row873_illegal : ¬ geometry.LegalContact rowPose873 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row873_reject_checked)
theorem row873_classified : RowClassified 873 := by
  intro p generated legal
  have he : rowPose873 = p := Option.some.inj (row873_generated.symm.trans generated)
  subst p
  exact (row873_illegal legal).elim

def rowPose874 : Pose 7 := ⟨perm101, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row874_fields : pairFieldsMatchB 188160 facet0 facet764 key0 key874 rowPose874 = true := by decide +kernel
theorem row874_generated : rootPair 874 = some rowPose874 :=
  pairFieldsMatchB_sound (by decide) row874_fields
theorem row874_source : sourceKey 874 ∈ geometry.profile (sourceOwner 874) := by decide +kernel
theorem row874_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 764 key1).FastValid geometry rowPose874 := by decide +kernel
theorem row874_illegal : ¬ geometry.LegalContact rowPose874 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row874_reject_checked)
theorem row874_classified : RowClassified 874 := by
  intro p generated legal
  have he : rowPose874 = p := Option.some.inj (row874_generated.symm.trans generated)
  subst p
  exact (row874_illegal legal).elim

def rowPose875 : Pose 7 := ⟨perm0, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row875_fields : pairFieldsMatchB 188160 facet0 facet765 key0 key875 rowPose875 = true := by decide +kernel
theorem row875_generated : rootPair 875 = some rowPose875 :=
  pairFieldsMatchB_sound (by decide) row875_fields
theorem row875_source : sourceKey 875 ∈ geometry.profile (sourceOwner 875) := by decide +kernel
theorem row875_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 758 key8).FastValid geometry rowPose875 := by decide +kernel
theorem row875_illegal : ¬ geometry.LegalContact rowPose875 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row875_reject_checked)
theorem row875_classified : RowClassified 875 := by
  intro p generated legal
  have he : rowPose875 = p := Option.some.inj (row875_generated.symm.trans generated)
  subst p
  exact (row875_illegal legal).elim

def rowPose876 : Pose 7 := ⟨perm15, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row876_fields : pairFieldsMatchB 188160 facet0 facet765 key0 key876 rowPose876 = true := by decide +kernel
theorem row876_generated : rootPair 876 = some rowPose876 :=
  pairFieldsMatchB_sound (by decide) row876_fields
theorem row876_source : sourceKey 876 ∈ geometry.profile (sourceOwner 876) := by decide +kernel
theorem row876_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 765 key0).FastValid geometry rowPose876 := by decide +kernel
theorem row876_illegal : ¬ geometry.LegalContact rowPose876 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row876_reject_checked)
theorem row876_classified : RowClassified 876 := by
  intro p generated legal
  have he : rowPose876 = p := Option.some.inj (row876_generated.symm.trans generated)
  subst p
  exact (row876_illegal legal).elim

def rowPose877 : Pose 7 := ⟨perm21, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row877_fields : pairFieldsMatchB 188160 facet0 facet766 key0 key877 rowPose877 = true := by decide +kernel
theorem row877_generated : rootPair 877 = some rowPose877 :=
  pairFieldsMatchB_sound (by decide) row877_fields
theorem row877_source : sourceKey 877 ∈ geometry.profile (sourceOwner 877) := by decide +kernel
theorem row877_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 766 key0).FastValid geometry rowPose877 := by decide +kernel
theorem row877_illegal : ¬ geometry.LegalContact rowPose877 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row877_reject_checked)
theorem row877_classified : RowClassified 877 := by
  intro p generated legal
  have he : rowPose877 = p := Option.some.inj (row877_generated.symm.trans generated)
  subst p
  exact (row877_illegal legal).elim

def rowPose878 : Pose 7 := ⟨perm42, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row878_fields : pairFieldsMatchB 188160 facet0 facet767 key0 key878 rowPose878 = true := by decide +kernel
theorem row878_generated : rootPair 878 = some rowPose878 :=
  pairFieldsMatchB_sound (by decide) row878_fields
theorem row878_source : sourceKey 878 ∈ geometry.profile (sourceOwner 878) := by decide +kernel
theorem row878_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 767 key0).FastValid geometry rowPose878 := by decide +kernel
theorem row878_illegal : ¬ geometry.LegalContact rowPose878 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row878_reject_checked)
theorem row878_classified : RowClassified 878 := by
  intro p generated legal
  have he : rowPose878 = p := Option.some.inj (row878_generated.symm.trans generated)
  subst p
  exact (row878_illegal legal).elim

def rowPose879 : Pose 7 := ⟨perm55, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row879_fields : pairFieldsMatchB 188160 facet0 facet768 key0 key879 rowPose879 = true := by decide +kernel
theorem row879_generated : rootPair 879 = some rowPose879 :=
  pairFieldsMatchB_sound (by decide) row879_fields
theorem row879_source : sourceKey 879 ∈ geometry.profile (sourceOwner 879) := by decide +kernel
theorem row879_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 768 key1).FastValid geometry rowPose879 := by decide +kernel
theorem row879_illegal : ¬ geometry.LegalContact rowPose879 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row879_reject_checked)
theorem row879_classified : RowClassified 879 := by
  intro p generated legal
  have he : rowPose879 = p := Option.some.inj (row879_generated.symm.trans generated)
  subst p
  exact (row879_illegal legal).elim

def rowPose880 : Pose 7 := ⟨perm73, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row880_fields : pairFieldsMatchB 188160 facet0 facet769 key0 key880 rowPose880 = true := by decide +kernel
theorem row880_generated : rootPair 880 = some rowPose880 :=
  pairFieldsMatchB_sound (by decide) row880_fields
theorem row880_source : sourceKey 880 ∈ geometry.profile (sourceOwner 880) := by decide +kernel
theorem row880_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 769 key0).FastValid geometry rowPose880 := by decide +kernel
theorem row880_illegal : ¬ geometry.LegalContact rowPose880 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row880_reject_checked)
theorem row880_classified : RowClassified 880 := by
  intro p generated legal
  have he : rowPose880 = p := Option.some.inj (row880_generated.symm.trans generated)
  subst p
  exact (row880_illegal legal).elim

def rowPose881 : Pose 7 := ⟨perm87, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row881_fields : pairFieldsMatchB 188160 facet0 facet770 key0 key881 rowPose881 = true := by decide +kernel
theorem row881_generated : rootPair 881 = some rowPose881 :=
  pairFieldsMatchB_sound (by decide) row881_fields
theorem row881_source : sourceKey 881 ∈ geometry.profile (sourceOwner 881) := by decide +kernel
theorem row881_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 770 key1).FastValid geometry rowPose881 := by decide +kernel
theorem row881_illegal : ¬ geometry.LegalContact rowPose881 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row881_reject_checked)
theorem row881_classified : RowClassified 881 := by
  intro p generated legal
  have he : rowPose881 = p := Option.some.inj (row881_generated.symm.trans generated)
  subst p
  exact (row881_illegal legal).elim

def rowPose882 : Pose 7 := ⟨perm96, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row882_fields : pairFieldsMatchB 188160 facet0 facet771 key0 key882 rowPose882 = true := by decide +kernel
theorem row882_generated : rootPair 882 = some rowPose882 :=
  pairFieldsMatchB_sound (by decide) row882_fields
theorem row882_source : sourceKey 882 ∈ geometry.profile (sourceOwner 882) := by decide +kernel
theorem row882_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 771 key1).FastValid geometry rowPose882 := by decide +kernel
theorem row882_illegal : ¬ geometry.LegalContact rowPose882 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row882_reject_checked)
theorem row882_classified : RowClassified 882 := by
  intro p generated legal
  have he : rowPose882 = p := Option.some.inj (row882_generated.symm.trans generated)
  subst p
  exact (row882_illegal legal).elim

def rowPose883 : Pose 7 := ⟨perm10, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row883_fields : pairFieldsMatchB 188160 facet0 facet772 key0 key883 rowPose883 = true := by decide +kernel
theorem row883_generated : rootPair 883 = some rowPose883 :=
  pairFieldsMatchB_sound (by decide) row883_fields
theorem row883_source : sourceKey 883 ∈ geometry.profile (sourceOwner 883) := by decide +kernel
theorem row883_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 772 key1).FastValid geometry rowPose883 := by decide +kernel
theorem row883_illegal : ¬ geometry.LegalContact rowPose883 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row883_reject_checked)
theorem row883_classified : RowClassified 883 := by
  intro p generated legal
  have he : rowPose883 = p := Option.some.inj (row883_generated.symm.trans generated)
  subst p
  exact (row883_illegal legal).elim

def rowPose884 : Pose 7 := ⟨perm22, ![false, true, true, false, false, true, true], ![-2, 1, 2, 0, -1, 2, 2]⟩
theorem row884_fields : pairFieldsMatchB 188160 facet0 facet773 key0 key884 rowPose884 = true := by decide +kernel
theorem row884_generated : rootPair 884 = some rowPose884 :=
  pairFieldsMatchB_sound (by decide) row884_fields
theorem row884_source : sourceKey 884 ∈ geometry.profile (sourceOwner 884) := by decide +kernel
theorem row884_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 773 key0).FastValid geometry rowPose884 := by decide +kernel
theorem row884_illegal : ¬ geometry.LegalContact rowPose884 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row884_reject_checked)
theorem row884_classified : RowClassified 884 := by
  intro p generated legal
  have he : rowPose884 = p := Option.some.inj (row884_generated.symm.trans generated)
  subst p
  exact (row884_illegal legal).elim

def rowPose885 : Pose 7 := ⟨perm37, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row885_fields : pairFieldsMatchB 188160 facet0 facet774 key0 key885 rowPose885 = true := by decide +kernel
theorem row885_generated : rootPair 885 = some rowPose885 :=
  pairFieldsMatchB_sound (by decide) row885_fields
theorem row885_source : sourceKey 885 ∈ geometry.profile (sourceOwner 885) := by decide +kernel
theorem row885_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 774 key1).FastValid geometry rowPose885 := by decide +kernel
theorem row885_illegal : ¬ geometry.LegalContact rowPose885 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row885_reject_checked)
theorem row885_classified : RowClassified 885 := by
  intro p generated legal
  have he : rowPose885 = p := Option.some.inj (row885_generated.symm.trans generated)
  subst p
  exact (row885_illegal legal).elim

def rowPose886 : Pose 7 := ⟨perm58, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row886_fields : pairFieldsMatchB 188160 facet0 facet775 key0 key886 rowPose886 = true := by decide +kernel
theorem row886_generated : rootPair 886 = some rowPose886 :=
  pairFieldsMatchB_sound (by decide) row886_fields
theorem row886_source : sourceKey 886 ∈ geometry.profile (sourceOwner 886) := by decide +kernel
theorem row886_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 775 key1).FastValid geometry rowPose886 := by decide +kernel
theorem row886_illegal : ¬ geometry.LegalContact rowPose886 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row886_reject_checked)
theorem row886_classified : RowClassified 886 := by
  intro p generated legal
  have he : rowPose886 = p := Option.some.inj (row886_generated.symm.trans generated)
  subst p
  exact (row886_illegal legal).elim

def rowPose887 : Pose 7 := ⟨perm74, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row887_fields : pairFieldsMatchB 188160 facet0 facet776 key0 key887 rowPose887 = true := by decide +kernel
theorem row887_generated : rootPair 887 = some rowPose887 :=
  pairFieldsMatchB_sound (by decide) row887_fields
theorem row887_source : sourceKey 887 ∈ geometry.profile (sourceOwner 887) := by decide +kernel
theorem row887_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 720 key8).FastValid geometry rowPose887 := by decide +kernel
theorem row887_illegal : ¬ geometry.LegalContact rowPose887 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row887_reject_checked)
theorem row887_classified : RowClassified 887 := by
  intro p generated legal
  have he : rowPose887 = p := Option.some.inj (row887_generated.symm.trans generated)
  subst p
  exact (row887_illegal legal).elim

def rowPose888 : Pose 7 := ⟨perm69, ![false, true, false, true, true, false, true], ![-2, 2, 0, 2, 2, 0, 2]⟩
theorem row888_fields : pairFieldsMatchB 188160 facet0 facet776 key0 key888 rowPose888 = true := by decide +kernel
theorem row888_generated : rootPair 888 = some rowPose888 :=
  pairFieldsMatchB_sound (by decide) row888_fields
theorem row888_source : sourceKey 888 ∈ geometry.profile (sourceOwner 888) := by decide +kernel
theorem row888_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 776 key0).FastValid geometry rowPose888 := by decide +kernel
theorem row888_illegal : ¬ geometry.LegalContact rowPose888 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row888_reject_checked)
theorem row888_classified : RowClassified 888 := by
  intro p generated legal
  have he : rowPose888 = p := Option.some.inj (row888_generated.symm.trans generated)
  subst p
  exact (row888_illegal legal).elim

def rowPose889 : Pose 7 := ⟨perm87, ![false, false, true, false, false, false, true], ![-2, -1, 2, 0, -1, -1, 1]⟩
theorem row889_fields : pairFieldsMatchB 188160 facet0 facet777 key0 key889 rowPose889 = true := by decide +kernel
theorem row889_generated : rootPair 889 = some rowPose889 :=
  pairFieldsMatchB_sound (by decide) row889_fields
theorem row889_source : sourceKey 889 ∈ geometry.profile (sourceOwner 889) := by decide +kernel
theorem row889_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 777 key0).FastValid geometry rowPose889 := by decide +kernel
theorem row889_illegal : ¬ geometry.LegalContact rowPose889 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row889_reject_checked)
theorem row889_classified : RowClassified 889 := by
  intro p generated legal
  have he : rowPose889 = p := Option.some.inj (row889_generated.symm.trans generated)
  subst p
  exact (row889_illegal legal).elim

def rowPose890 : Pose 7 := ⟨perm96, ![true, false, true, false, true, false, false], ![0, -1, 2, 0, 2, -1, -1]⟩
theorem row890_fields : pairFieldsMatchB 188160 facet0 facet778 key0 key890 rowPose890 = true := by decide +kernel
theorem row890_generated : rootPair 890 = some rowPose890 :=
  pairFieldsMatchB_sound (by decide) row890_fields
theorem row890_source : sourceKey 890 ∈ geometry.profile (sourceOwner 890) := by decide +kernel
theorem row890_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 778 key0).FastValid geometry rowPose890 := by decide +kernel
theorem row890_illegal : ¬ geometry.LegalContact rowPose890 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row890_reject_checked)
theorem row890_classified : RowClassified 890 := by
  intro p generated legal
  have he : rowPose890 = p := Option.some.inj (row890_generated.symm.trans generated)
  subst p
  exact (row890_illegal legal).elim

def rowPose891 : Pose 7 := ⟨perm15, ![false, false, true, true, true, true, false], ![-2, -1, 2, 2, 2, 1, -1]⟩
theorem row891_fields : pairFieldsMatchB 188160 facet0 facet779 key0 key891 rowPose891 = true := by decide +kernel
theorem row891_generated : rootPair 891 = some rowPose891 :=
  pairFieldsMatchB_sound (by decide) row891_fields
theorem row891_source : sourceKey 891 ∈ geometry.profile (sourceOwner 891) := by decide +kernel
theorem row891_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 779 key0).FastValid geometry rowPose891 := by decide +kernel
theorem row891_illegal : ¬ geometry.LegalContact rowPose891 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row891_reject_checked)
theorem row891_classified : RowClassified 891 := by
  intro p generated legal
  have he : rowPose891 = p := Option.some.inj (row891_generated.symm.trans generated)
  subst p
  exact (row891_illegal legal).elim

def rowPose892 : Pose 7 := ⟨perm24, ![false, true, true, true, false, false, false], ![-2, 1, 2, 2, -1, -1, -1]⟩
theorem row892_fields : pairFieldsMatchB 188160 facet0 facet780 key0 key892 rowPose892 = true := by decide +kernel
theorem row892_generated : rootPair 892 = some rowPose892 :=
  pairFieldsMatchB_sound (by decide) row892_fields
theorem row892_source : sourceKey 892 ∈ geometry.profile (sourceOwner 892) := by decide +kernel
theorem row892_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 780 key0).FastValid geometry rowPose892 := by decide +kernel
theorem row892_illegal : ¬ geometry.LegalContact rowPose892 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row892_reject_checked)
theorem row892_classified : RowClassified 892 := by
  intro p generated legal
  have he : rowPose892 = p := Option.some.inj (row892_generated.symm.trans generated)
  subst p
  exact (row892_illegal legal).elim

def rowPose893 : Pose 7 := ⟨perm37, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row893_fields : pairFieldsMatchB 188160 facet0 facet781 key0 key893 rowPose893 = true := by decide +kernel
theorem row893_generated : rootPair 893 = some rowPose893 :=
  pairFieldsMatchB_sound (by decide) row893_fields
theorem row893_source : sourceKey 893 ∈ geometry.profile (sourceOwner 893) := by decide +kernel
theorem row893_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 725 key8).FastValid geometry rowPose893 := by decide +kernel
theorem row893_illegal : ¬ geometry.LegalContact rowPose893 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row893_reject_checked)
theorem row893_classified : RowClassified 893 := by
  intro p generated legal
  have he : rowPose893 = p := Option.some.inj (row893_generated.symm.trans generated)
  subst p
  exact (row893_illegal legal).elim

def rowPose894 : Pose 7 := ⟨perm42, ![true, true, true, true, true, true, true], ![0, 2, 2, 2, 2, 2, 2]⟩
theorem row894_fields : pairFieldsMatchB 188160 facet0 facet781 key0 key894 rowPose894 = true := by decide +kernel
theorem row894_generated : rootPair 894 = some rowPose894 :=
  pairFieldsMatchB_sound (by decide) row894_fields
theorem row894_source : sourceKey 894 ∈ geometry.profile (sourceOwner 894) := by decide +kernel
theorem row894_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 781 key0).FastValid geometry rowPose894 := by decide +kernel
theorem row894_illegal : ¬ geometry.LegalContact rowPose894 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row894_reject_checked)
theorem row894_classified : RowClassified 894 := by
  intro p generated legal
  have he : rowPose894 = p := Option.some.inj (row894_generated.symm.trans generated)
  subst p
  exact (row894_illegal legal).elim

def rowPose895 : Pose 7 := ⟨perm42, ![false, true, false, false, false, true, true], ![-1, 2, -1, -1, -1, 2, 2]⟩
theorem row895_fields : pairFieldsMatchB 188160 facet0 facet782 key0 key895 rowPose895 = true := by decide +kernel
theorem row895_generated : rootPair 895 = some rowPose895 :=
  pairFieldsMatchB_sound (by decide) row895_fields
theorem row895_source : sourceKey 895 ∈ geometry.profile (sourceOwner 895) := by decide +kernel
theorem row895_reject_checked : (show IndexedRejection 7 896 from .overlap ![0, 1, 0, 0, 0, 1, 0]).FastValid geometry rowPose895 := by decide +kernel
theorem row895_illegal : ¬ geometry.LegalContact rowPose895 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row895_reject_checked)
theorem row895_classified : RowClassified 895 := by
  intro p generated legal
  have he : rowPose895 = p := Option.some.inj (row895_generated.symm.trans generated)
  subst p
  exact (row895_illegal legal).elim

theorem chunk27_classified (i : Fin 32) : RowClassified ⟨864 + i.val, by omega⟩ := by
  fin_cases i
  · exact row864_classified
  · exact row865_classified
  · exact row866_classified
  · exact row867_classified
  · exact row868_classified
  · exact row869_classified
  · exact row870_classified
  · exact row871_classified
  · exact row872_classified
  · exact row873_classified
  · exact row874_classified
  · exact row875_classified
  · exact row876_classified
  · exact row877_classified
  · exact row878_classified
  · exact row879_classified
  · exact row880_classified
  · exact row881_classified
  · exact row882_classified
  · exact row883_classified
  · exact row884_classified
  · exact row885_classified
  · exact row886_classified
  · exact row887_classified
  · exact row888_classified
  · exact row889_classified
  · exact row890_classified
  · exact row891_classified
  · exact row892_classified
  · exact row893_classified
  · exact row894_classified
  · exact row895_classified

theorem chunk27_source (i : Fin 32) : sourceKey ⟨864 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨864 + i.val, by omega⟩) := by
  fin_cases i
  · exact row864_source
  · exact row865_source
  · exact row866_source
  · exact row867_source
  · exact row868_source
  · exact row869_source
  · exact row870_source
  · exact row871_source
  · exact row872_source
  · exact row873_source
  · exact row874_source
  · exact row875_source
  · exact row876_source
  · exact row877_source
  · exact row878_source
  · exact row879_source
  · exact row880_source
  · exact row881_source
  · exact row882_source
  · exact row883_source
  · exact row884_source
  · exact row885_source
  · exact row886_source
  · exact row887_source
  · exact row888_source
  · exact row889_source
  · exact row890_source
  · exact row891_source
  · exact row892_source
  · exact row893_source
  · exact row894_source
  · exact row895_source

#print axioms chunk27_classified
end SparseMonotiles.Contact.RootZeroPilot7
