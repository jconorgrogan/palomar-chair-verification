module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose96 : Pose 7 := ⟨perm0, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row96_fields : pairFieldsMatchB 188160 facet0 facet84 key0 key96 rowPose96 = true := by decide +kernel
theorem row96_generated : rootPair 96 = some rowPose96 :=
  pairFieldsMatchB_sound (by decide) row96_fields
theorem row96_source : sourceKey 96 ∈ geometry.profile (sourceOwner 96) := by decide +kernel
theorem row96_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 84 key0).FastValid geometry rowPose96 := by decide +kernel
theorem row96_illegal : ¬ geometry.LegalContact rowPose96 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row96_reject_checked)
theorem row96_classified : RowClassified 96 := by
  intro p generated legal
  have he : rowPose96 = p := Option.some.inj (row96_generated.symm.trans generated)
  subst p
  exact (row96_illegal legal).elim

def rowPose97 : Pose 7 := ⟨perm15, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row97_fields : pairFieldsMatchB 188160 facet0 facet84 key0 key97 rowPose97 = true := by decide +kernel
theorem row97_generated : rootPair 97 = some rowPose97 :=
  pairFieldsMatchB_sound (by decide) row97_fields
theorem row97_source : sourceKey 97 ∈ geometry.profile (sourceOwner 97) := by decide +kernel
theorem row97_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 308 key8).FastValid geometry rowPose97 := by decide +kernel
theorem row97_illegal : ¬ geometry.LegalContact rowPose97 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row97_reject_checked)
theorem row97_classified : RowClassified 97 := by
  intro p generated legal
  have he : rowPose97 = p := Option.some.inj (row97_generated.symm.trans generated)
  subst p
  exact (row97_illegal legal).elim

def rowPose98 : Pose 7 := ⟨perm21, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row98_fields : pairFieldsMatchB 188160 facet0 facet85 key0 key98 rowPose98 = true := by decide +kernel
theorem row98_generated : rootPair 98 = some rowPose98 :=
  pairFieldsMatchB_sound (by decide) row98_fields
theorem row98_source : sourceKey 98 ∈ geometry.profile (sourceOwner 98) := by decide +kernel
theorem row98_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 85 key1).FastValid geometry rowPose98 := by decide +kernel
theorem row98_illegal : ¬ geometry.LegalContact rowPose98 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row98_reject_checked)
theorem row98_classified : RowClassified 98 := by
  intro p generated legal
  have he : rowPose98 = p := Option.some.inj (row98_generated.symm.trans generated)
  subst p
  exact (row98_illegal legal).elim

def rowPose99 : Pose 7 := ⟨perm42, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row99_fields : pairFieldsMatchB 188160 facet0 facet86 key0 key99 rowPose99 = true := by decide +kernel
theorem row99_generated : rootPair 99 = some rowPose99 :=
  pairFieldsMatchB_sound (by decide) row99_fields
theorem row99_source : sourceKey 99 ∈ geometry.profile (sourceOwner 99) := by decide +kernel
theorem row99_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 86 key1).FastValid geometry rowPose99 := by decide +kernel
theorem row99_illegal : ¬ geometry.LegalContact rowPose99 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row99_reject_checked)
theorem row99_classified : RowClassified 99 := by
  intro p generated legal
  have he : rowPose99 = p := Option.some.inj (row99_generated.symm.trans generated)
  subst p
  exact (row99_illegal legal).elim

def rowPose100 : Pose 7 := ⟨perm55, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row100_fields : pairFieldsMatchB 188160 facet0 facet87 key0 key100 rowPose100 = true := by decide +kernel
theorem row100_generated : rootPair 100 = some rowPose100 :=
  pairFieldsMatchB_sound (by decide) row100_fields
theorem row100_source : sourceKey 100 ∈ geometry.profile (sourceOwner 100) := by decide +kernel
theorem row100_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 87 key0).FastValid geometry rowPose100 := by decide +kernel
theorem row100_illegal : ¬ geometry.LegalContact rowPose100 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row100_reject_checked)
theorem row100_classified : RowClassified 100 := by
  intro p generated legal
  have he : rowPose100 = p := Option.some.inj (row100_generated.symm.trans generated)
  subst p
  exact (row100_illegal legal).elim

def rowPose101 : Pose 7 := ⟨perm73, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row101_fields : pairFieldsMatchB 188160 facet0 facet88 key0 key101 rowPose101 = true := by decide +kernel
theorem row101_generated : rootPair 101 = some rowPose101 :=
  pairFieldsMatchB_sound (by decide) row101_fields
theorem row101_source : sourceKey 101 ∈ geometry.profile (sourceOwner 101) := by decide +kernel
theorem row101_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 88 key1).FastValid geometry rowPose101 := by decide +kernel
theorem row101_illegal : ¬ geometry.LegalContact rowPose101 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row101_reject_checked)
theorem row101_classified : RowClassified 101 := by
  intro p generated legal
  have he : rowPose101 = p := Option.some.inj (row101_generated.symm.trans generated)
  subst p
  exact (row101_illegal legal).elim

def rowPose102 : Pose 7 := ⟨perm87, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row102_fields : pairFieldsMatchB 188160 facet0 facet89 key0 key102 rowPose102 = true := by decide +kernel
theorem row102_generated : rootPair 102 = some rowPose102 :=
  pairFieldsMatchB_sound (by decide) row102_fields
theorem row102_source : sourceKey 102 ∈ geometry.profile (sourceOwner 102) := by decide +kernel
theorem row102_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 89 key0).FastValid geometry rowPose102 := by decide +kernel
theorem row102_illegal : ¬ geometry.LegalContact rowPose102 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row102_reject_checked)
theorem row102_classified : RowClassified 102 := by
  intro p generated legal
  have he : rowPose102 = p := Option.some.inj (row102_generated.symm.trans generated)
  subst p
  exact (row102_illegal legal).elim

def rowPose103 : Pose 7 := ⟨perm96, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row103_fields : pairFieldsMatchB 188160 facet0 facet90 key0 key103 rowPose103 = true := by decide +kernel
theorem row103_generated : rootPair 103 = some rowPose103 :=
  pairFieldsMatchB_sound (by decide) row103_fields
theorem row103_source : sourceKey 103 ∈ geometry.profile (sourceOwner 103) := by decide +kernel
theorem row103_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 90 key0).FastValid geometry rowPose103 := by decide +kernel
theorem row103_illegal : ¬ geometry.LegalContact rowPose103 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row103_reject_checked)
theorem row103_classified : RowClassified 103 := by
  intro p generated legal
  have he : rowPose103 = p := Option.some.inj (row103_generated.symm.trans generated)
  subst p
  exact (row103_illegal legal).elim

def rowPose104 : Pose 7 := ⟨perm15, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row104_fields : pairFieldsMatchB 188160 facet0 facet91 key0 key104 rowPose104 = true := by decide +kernel
theorem row104_generated : rootPair 104 = some rowPose104 :=
  pairFieldsMatchB_sound (by decide) row104_fields
theorem row104_source : sourceKey 104 ∈ geometry.profile (sourceOwner 104) := by decide +kernel
theorem row104_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 91 key1).FastValid geometry rowPose104 := by decide +kernel
theorem row104_illegal : ¬ geometry.LegalContact rowPose104 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row104_reject_checked)
theorem row104_classified : RowClassified 104 := by
  intro p generated legal
  have he : rowPose104 = p := Option.some.inj (row104_generated.symm.trans generated)
  subst p
  exact (row104_illegal legal).elim

def rowPose105 : Pose 7 := ⟨perm24, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row105_fields : pairFieldsMatchB 188160 facet0 facet92 key0 key105 rowPose105 = true := by decide +kernel
theorem row105_generated : rootPair 105 = some rowPose105 :=
  pairFieldsMatchB_sound (by decide) row105_fields
theorem row105_source : sourceKey 105 ∈ geometry.profile (sourceOwner 105) := by decide +kernel
theorem row105_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 92 key1).FastValid geometry rowPose105 := by decide +kernel
theorem row105_illegal : ¬ geometry.LegalContact rowPose105 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row105_reject_checked)
theorem row105_classified : RowClassified 105 := by
  intro p generated legal
  have he : rowPose105 = p := Option.some.inj (row105_generated.symm.trans generated)
  subst p
  exact (row105_illegal legal).elim

def rowPose106 : Pose 7 := ⟨perm37, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row106_fields : pairFieldsMatchB 188160 facet0 facet93 key0 key106 rowPose106 = true := by decide +kernel
theorem row106_generated : rootPair 106 = some rowPose106 :=
  pairFieldsMatchB_sound (by decide) row106_fields
theorem row106_source : sourceKey 106 ∈ geometry.profile (sourceOwner 106) := by decide +kernel
theorem row106_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 93 key0).FastValid geometry rowPose106 := by decide +kernel
theorem row106_illegal : ¬ geometry.LegalContact rowPose106 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row106_reject_checked)
theorem row106_classified : RowClassified 106 := by
  intro p generated legal
  have he : rowPose106 = p := Option.some.inj (row106_generated.symm.trans generated)
  subst p
  exact (row106_illegal legal).elim

def rowPose107 : Pose 7 := ⟨perm42, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row107_fields : pairFieldsMatchB 188160 facet0 facet93 key0 key107 rowPose107 = true := by decide +kernel
theorem row107_generated : rootPair 107 = some rowPose107 :=
  pairFieldsMatchB_sound (by decide) row107_fields
theorem row107_source : sourceKey 107 ∈ geometry.profile (sourceOwner 107) := by decide +kernel
theorem row107_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 317 key8).FastValid geometry rowPose107 := by decide +kernel
theorem row107_illegal : ¬ geometry.LegalContact rowPose107 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row107_reject_checked)
theorem row107_classified : RowClassified 107 := by
  intro p generated legal
  have he : rowPose107 = p := Option.some.inj (row107_generated.symm.trans generated)
  subst p
  exact (row107_illegal legal).elim

def rowPose108 : Pose 7 := ⟨perm53, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row108_fields : pairFieldsMatchB 188160 facet0 facet94 key0 key108 rowPose108 = true := by decide +kernel
theorem row108_generated : rootPair 108 = some rowPose108 :=
  pairFieldsMatchB_sound (by decide) row108_fields
theorem row108_source : sourceKey 108 ∈ geometry.profile (sourceOwner 108) := by decide +kernel
theorem row108_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 94 key0).FastValid geometry rowPose108 := by decide +kernel
theorem row108_illegal : ¬ geometry.LegalContact rowPose108 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row108_reject_checked)
theorem row108_classified : RowClassified 108 := by
  intro p generated legal
  have he : rowPose108 = p := Option.some.inj (row108_generated.symm.trans generated)
  subst p
  exact (row108_illegal legal).elim

def rowPose109 : Pose 7 := ⟨perm74, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row109_fields : pairFieldsMatchB 188160 facet0 facet95 key0 key109 rowPose109 = true := by decide +kernel
theorem row109_generated : rootPair 109 = some rowPose109 :=
  pairFieldsMatchB_sound (by decide) row109_fields
theorem row109_source : sourceKey 109 ∈ geometry.profile (sourceOwner 109) := by decide +kernel
theorem row109_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 95 key0).FastValid geometry rowPose109 := by decide +kernel
theorem row109_illegal : ¬ geometry.LegalContact rowPose109 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row109_reject_checked)
theorem row109_classified : RowClassified 109 := by
  intro p generated legal
  have he : rowPose109 = p := Option.some.inj (row109_generated.symm.trans generated)
  subst p
  exact (row109_illegal legal).elim

def rowPose110 : Pose 7 := ⟨perm89, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row110_fields : pairFieldsMatchB 188160 facet0 facet96 key0 key110 rowPose110 = true := by decide +kernel
theorem row110_generated : rootPair 110 = some rowPose110 :=
  pairFieldsMatchB_sound (by decide) row110_fields
theorem row110_source : sourceKey 110 ∈ geometry.profile (sourceOwner 110) := by decide +kernel
theorem row110_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 96 key1).FastValid geometry rowPose110 := by decide +kernel
theorem row110_illegal : ¬ geometry.LegalContact rowPose110 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row110_reject_checked)
theorem row110_classified : RowClassified 110 := by
  intro p generated legal
  have he : rowPose110 = p := Option.some.inj (row110_generated.symm.trans generated)
  subst p
  exact (row110_illegal legal).elim

def rowPose111 : Pose 7 := ⟨perm101, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row111_fields : pairFieldsMatchB 188160 facet0 facet97 key0 key111 rowPose111 = true := by decide +kernel
theorem row111_generated : rootPair 111 = some rowPose111 :=
  pairFieldsMatchB_sound (by decide) row111_fields
theorem row111_source : sourceKey 111 ∈ geometry.profile (sourceOwner 111) := by decide +kernel
theorem row111_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 97 key0).FastValid geometry rowPose111 := by decide +kernel
theorem row111_illegal : ¬ geometry.LegalContact rowPose111 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row111_reject_checked)
theorem row111_classified : RowClassified 111 := by
  intro p generated legal
  have he : rowPose111 = p := Option.some.inj (row111_generated.symm.trans generated)
  subst p
  exact (row111_illegal legal).elim

def rowPose112 : Pose 7 := ⟨perm10, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row112_fields : pairFieldsMatchB 188160 facet0 facet98 key0 key112 rowPose112 = true := by decide +kernel
theorem row112_generated : rootPair 112 = some rowPose112 :=
  pairFieldsMatchB_sound (by decide) row112_fields
theorem row112_source : sourceKey 112 ∈ geometry.profile (sourceOwner 112) := by decide +kernel
theorem row112_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 98 key1).FastValid geometry rowPose112 := by decide +kernel
theorem row112_illegal : ¬ geometry.LegalContact rowPose112 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row112_reject_checked)
theorem row112_classified : RowClassified 112 := by
  intro p generated legal
  have he : rowPose112 = p := Option.some.inj (row112_generated.symm.trans generated)
  subst p
  exact (row112_illegal legal).elim

def rowPose113 : Pose 7 := ⟨perm22, ![true, true, false, false, false, true, true], ![0, 1, 0, 0, -1, 2, 2]⟩
theorem row113_fields : pairFieldsMatchB 188160 facet0 facet99 key0 key113 rowPose113 = true := by decide +kernel
theorem row113_generated : rootPair 113 = some rowPose113 :=
  pairFieldsMatchB_sound (by decide) row113_fields
theorem row113_source : sourceKey 113 ∈ geometry.profile (sourceOwner 113) := by decide +kernel
theorem row113_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 99 key0).FastValid geometry rowPose113 := by decide +kernel
theorem row113_illegal : ¬ geometry.LegalContact rowPose113 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row113_reject_checked)
theorem row113_classified : RowClassified 113 := by
  intro p generated legal
  have he : rowPose113 = p := Option.some.inj (row113_generated.symm.trans generated)
  subst p
  exact (row113_illegal legal).elim

def rowPose114 : Pose 7 := ⟨perm37, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row114_fields : pairFieldsMatchB 188160 facet0 facet100 key0 key114 rowPose114 = true := by decide +kernel
theorem row114_generated : rootPair 114 = some rowPose114 :=
  pairFieldsMatchB_sound (by decide) row114_fields
theorem row114_source : sourceKey 114 ∈ geometry.profile (sourceOwner 114) := by decide +kernel
theorem row114_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 100 key1).FastValid geometry rowPose114 := by decide +kernel
theorem row114_illegal : ¬ geometry.LegalContact rowPose114 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row114_reject_checked)
theorem row114_classified : RowClassified 114 := by
  intro p generated legal
  have he : rowPose114 = p := Option.some.inj (row114_generated.symm.trans generated)
  subst p
  exact (row114_illegal legal).elim

def rowPose115 : Pose 7 := ⟨perm58, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row115_fields : pairFieldsMatchB 188160 facet0 facet101 key0 key115 rowPose115 = true := by decide +kernel
theorem row115_generated : rootPair 115 = some rowPose115 :=
  pairFieldsMatchB_sound (by decide) row115_fields
theorem row115_source : sourceKey 115 ∈ geometry.profile (sourceOwner 115) := by decide +kernel
theorem row115_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 101 key1).FastValid geometry rowPose115 := by decide +kernel
theorem row115_illegal : ¬ geometry.LegalContact rowPose115 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row115_reject_checked)
theorem row115_classified : RowClassified 115 := by
  intro p generated legal
  have he : rowPose115 = p := Option.some.inj (row115_generated.symm.trans generated)
  subst p
  exact (row115_illegal legal).elim

def rowPose116 : Pose 7 := ⟨perm74, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row116_fields : pairFieldsMatchB 188160 facet0 facet102 key0 key116 rowPose116 = true := by decide +kernel
theorem row116_generated : rootPair 116 = some rowPose116 :=
  pairFieldsMatchB_sound (by decide) row116_fields
theorem row116_source : sourceKey 116 ∈ geometry.profile (sourceOwner 116) := by decide +kernel
theorem row116_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 46 key8).FastValid geometry rowPose116 := by decide +kernel
theorem row116_illegal : ¬ geometry.LegalContact rowPose116 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row116_reject_checked)
theorem row116_classified : RowClassified 116 := by
  intro p generated legal
  have he : rowPose116 = p := Option.some.inj (row116_generated.symm.trans generated)
  subst p
  exact (row116_illegal legal).elim

def rowPose117 : Pose 7 := ⟨perm69, ![false, true, false, false, false, false, true], ![-2, 2, 0, 0, 0, 0, 2]⟩
theorem row117_fields : pairFieldsMatchB 188160 facet0 facet102 key0 key117 rowPose117 = true := by decide +kernel
theorem row117_generated : rootPair 117 = some rowPose117 :=
  pairFieldsMatchB_sound (by decide) row117_fields
theorem row117_source : sourceKey 117 ∈ geometry.profile (sourceOwner 117) := by decide +kernel
theorem row117_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 102 key0).FastValid geometry rowPose117 := by decide +kernel
theorem row117_illegal : ¬ geometry.LegalContact rowPose117 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row117_reject_checked)
theorem row117_classified : RowClassified 117 := by
  intro p generated legal
  have he : rowPose117 = p := Option.some.inj (row117_generated.symm.trans generated)
  subst p
  exact (row117_illegal legal).elim

def rowPose118 : Pose 7 := ⟨perm87, ![false, false, true, false, true, true, true], ![-2, -1, 2, 0, 1, 1, 1]⟩
theorem row118_fields : pairFieldsMatchB 188160 facet0 facet103 key0 key118 rowPose118 = true := by decide +kernel
theorem row118_generated : rootPair 118 = some rowPose118 :=
  pairFieldsMatchB_sound (by decide) row118_fields
theorem row118_source : sourceKey 118 ∈ geometry.profile (sourceOwner 118) := by decide +kernel
theorem row118_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 103 key0).FastValid geometry rowPose118 := by decide +kernel
theorem row118_illegal : ¬ geometry.LegalContact rowPose118 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row118_reject_checked)
theorem row118_classified : RowClassified 118 := by
  intro p generated legal
  have he : rowPose118 = p := Option.some.inj (row118_generated.symm.trans generated)
  subst p
  exact (row118_illegal legal).elim

def rowPose119 : Pose 7 := ⟨perm96, ![true, true, false, false, true, false, false], ![0, 1, 0, 0, 2, -1, -1]⟩
theorem row119_fields : pairFieldsMatchB 188160 facet0 facet104 key0 key119 rowPose119 = true := by decide +kernel
theorem row119_generated : rootPair 119 = some rowPose119 :=
  pairFieldsMatchB_sound (by decide) row119_fields
theorem row119_source : sourceKey 119 ∈ geometry.profile (sourceOwner 119) := by decide +kernel
theorem row119_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 104 key0).FastValid geometry rowPose119 := by decide +kernel
theorem row119_illegal : ¬ geometry.LegalContact rowPose119 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row119_reject_checked)
theorem row119_classified : RowClassified 119 := by
  intro p generated legal
  have he : rowPose119 = p := Option.some.inj (row119_generated.symm.trans generated)
  subst p
  exact (row119_illegal legal).elim

def rowPose120 : Pose 7 := ⟨perm0, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row120_fields : pairFieldsMatchB 188160 facet0 facet105 key0 key120 rowPose120 = true := by decide +kernel
theorem row120_generated : rootPair 120 = some rowPose120 :=
  pairFieldsMatchB_sound (by decide) row120_fields
theorem row120_source : sourceKey 120 ∈ geometry.profile (sourceOwner 120) := by decide +kernel
theorem row120_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 105 key0).FastValid geometry rowPose120 := by decide +kernel
theorem row120_illegal : ¬ geometry.LegalContact rowPose120 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row120_reject_checked)
theorem row120_classified : RowClassified 120 := by
  intro p generated legal
  have he : rowPose120 = p := Option.some.inj (row120_generated.symm.trans generated)
  subst p
  exact (row120_illegal legal).elim

def rowPose121 : Pose 7 := ⟨perm21, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row121_fields : pairFieldsMatchB 188160 facet0 facet106 key0 key121 rowPose121 = true := by decide +kernel
theorem row121_generated : rootPair 121 = some rowPose121 :=
  pairFieldsMatchB_sound (by decide) row121_fields
theorem row121_source : sourceKey 121 ∈ geometry.profile (sourceOwner 121) := by decide +kernel
theorem row121_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 218 key8).FastValid geometry rowPose121 := by decide +kernel
theorem row121_illegal : ¬ geometry.LegalContact rowPose121 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row121_reject_checked)
theorem row121_classified : RowClassified 121 := by
  intro p generated legal
  have he : rowPose121 = p := Option.some.inj (row121_generated.symm.trans generated)
  subst p
  exact (row121_illegal legal).elim

def rowPose122 : Pose 7 := ⟨perm24, ![true, false, true, true, true, true, false], ![0, 0, 2, 2, 2, 2, 0]⟩
theorem row122_fields : pairFieldsMatchB 188160 facet0 facet106 key0 key122 rowPose122 = true := by decide +kernel
theorem row122_generated : rootPair 122 = some rowPose122 :=
  pairFieldsMatchB_sound (by decide) row122_fields
theorem row122_source : sourceKey 122 ∈ geometry.profile (sourceOwner 122) := by decide +kernel
theorem row122_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 106 key0).FastValid geometry rowPose122 := by decide +kernel
theorem row122_illegal : ¬ geometry.LegalContact rowPose122 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row122_reject_checked)
theorem row122_classified : RowClassified 122 := by
  intro p generated legal
  have he : rowPose122 = p := Option.some.inj (row122_generated.symm.trans generated)
  subst p
  exact (row122_illegal legal).elim

def rowPose123 : Pose 7 := ⟨perm37, ![true, true, false, true, false, false, false], ![0, 1, 0, 2, -1, -1, -1]⟩
theorem row123_fields : pairFieldsMatchB 188160 facet0 facet107 key0 key123 rowPose123 = true := by decide +kernel
theorem row123_generated : rootPair 123 = some rowPose123 :=
  pairFieldsMatchB_sound (by decide) row123_fields
theorem row123_source : sourceKey 123 ∈ geometry.profile (sourceOwner 123) := by decide +kernel
theorem row123_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 107 key1).FastValid geometry rowPose123 := by decide +kernel
theorem row123_illegal : ¬ geometry.LegalContact rowPose123 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row123_reject_checked)
theorem row123_classified : RowClassified 123 := by
  intro p generated legal
  have he : rowPose123 = p := Option.some.inj (row123_generated.symm.trans generated)
  subst p
  exact (row123_illegal legal).elim

def rowPose124 : Pose 7 := ⟨perm58, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row124_fields : pairFieldsMatchB 188160 facet0 facet108 key0 key124 rowPose124 = true := by decide +kernel
theorem row124_generated : rootPair 124 = some rowPose124 :=
  pairFieldsMatchB_sound (by decide) row124_fields
theorem row124_source : sourceKey 124 ∈ geometry.profile (sourceOwner 124) := by decide +kernel
theorem row124_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 108 key1).FastValid geometry rowPose124 := by decide +kernel
theorem row124_illegal : ¬ geometry.LegalContact rowPose124 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row124_reject_checked)
theorem row124_classified : RowClassified 124 := by
  intro p generated legal
  have he : rowPose124 = p := Option.some.inj (row124_generated.symm.trans generated)
  subst p
  exact (row124_illegal legal).elim

def rowPose125 : Pose 7 := ⟨perm71, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row125_fields : pairFieldsMatchB 188160 facet0 facet109 key0 key125 rowPose125 = true := by decide +kernel
theorem row125_generated : rootPair 125 = some rowPose125 :=
  pairFieldsMatchB_sound (by decide) row125_fields
theorem row125_source : sourceKey 125 ∈ geometry.profile (sourceOwner 125) := by decide +kernel
theorem row125_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 109 key0).FastValid geometry rowPose125 := by decide +kernel
theorem row125_illegal : ¬ geometry.LegalContact rowPose125 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row125_reject_checked)
theorem row125_classified : RowClassified 125 := by
  intro p generated legal
  have he : rowPose125 = p := Option.some.inj (row125_generated.symm.trans generated)
  subst p
  exact (row125_illegal legal).elim

def rowPose126 : Pose 7 := ⟨perm95, ![false, false, true, true, true, false, false], ![-2, -1, 2, 2, 1, 0, 0]⟩
theorem row126_fields : pairFieldsMatchB 188160 facet0 facet110 key0 key126 rowPose126 = true := by decide +kernel
theorem row126_generated : rootPair 126 = some rowPose126 :=
  pairFieldsMatchB_sound (by decide) row126_fields
theorem row126_source : sourceKey 126 ∈ geometry.profile (sourceOwner 126) := by decide +kernel
theorem row126_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 110 key1).FastValid geometry rowPose126 := by decide +kernel
theorem row126_illegal : ¬ geometry.LegalContact rowPose126 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row126_reject_checked)
theorem row126_classified : RowClassified 126 := by
  intro p generated legal
  have he : rowPose126 = p := Option.some.inj (row126_generated.symm.trans generated)
  subst p
  exact (row126_illegal legal).elim

def rowPose127 : Pose 7 := ⟨perm111, ![false, false, true, true, false, true, true], ![-2, -1, 2, 2, 0, 1, 1]⟩
theorem row127_fields : pairFieldsMatchB 188160 facet0 facet111 key0 key127 rowPose127 = true := by decide +kernel
theorem row127_generated : rootPair 127 = some rowPose127 :=
  pairFieldsMatchB_sound (by decide) row127_fields
theorem row127_source : sourceKey 127 ∈ geometry.profile (sourceOwner 127) := by decide +kernel
theorem row127_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 111 key0).FastValid geometry rowPose127 := by decide +kernel
theorem row127_illegal : ¬ geometry.LegalContact rowPose127 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row127_reject_checked)
theorem row127_classified : RowClassified 127 := by
  intro p generated legal
  have he : rowPose127 = p := Option.some.inj (row127_generated.symm.trans generated)
  subst p
  exact (row127_illegal legal).elim

theorem chunk03_classified (i : Fin 32) : RowClassified ⟨96 + i.val, by omega⟩ := by
  fin_cases i
  · exact row96_classified
  · exact row97_classified
  · exact row98_classified
  · exact row99_classified
  · exact row100_classified
  · exact row101_classified
  · exact row102_classified
  · exact row103_classified
  · exact row104_classified
  · exact row105_classified
  · exact row106_classified
  · exact row107_classified
  · exact row108_classified
  · exact row109_classified
  · exact row110_classified
  · exact row111_classified
  · exact row112_classified
  · exact row113_classified
  · exact row114_classified
  · exact row115_classified
  · exact row116_classified
  · exact row117_classified
  · exact row118_classified
  · exact row119_classified
  · exact row120_classified
  · exact row121_classified
  · exact row122_classified
  · exact row123_classified
  · exact row124_classified
  · exact row125_classified
  · exact row126_classified
  · exact row127_classified

theorem chunk03_source (i : Fin 32) : sourceKey ⟨96 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨96 + i.val, by omega⟩) := by
  fin_cases i
  · exact row96_source
  · exact row97_source
  · exact row98_source
  · exact row99_source
  · exact row100_source
  · exact row101_source
  · exact row102_source
  · exact row103_source
  · exact row104_source
  · exact row105_source
  · exact row106_source
  · exact row107_source
  · exact row108_source
  · exact row109_source
  · exact row110_source
  · exact row111_source
  · exact row112_source
  · exact row113_source
  · exact row114_source
  · exact row115_source
  · exact row116_source
  · exact row117_source
  · exact row118_source
  · exact row119_source
  · exact row120_source
  · exact row121_source
  · exact row122_source
  · exact row123_source
  · exact row124_source
  · exact row125_source
  · exact row126_source
  · exact row127_source

#print axioms chunk03_classified
end SparseMonotiles.Contact.RootZeroPilot7
