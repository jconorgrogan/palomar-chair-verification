module
public import PilotBase
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace SparseMonotiles.Contact.RootZeroPilot7
open IndexedData7 CarrierHierarchy
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rowPose192 : Pose 7 := ⟨perm15, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row192_fields : pairFieldsMatchB 188160 facet0 facet168 key0 key192 rowPose192 = true := by decide +kernel
theorem row192_generated : rootPair 192 = some rowPose192 :=
  pairFieldsMatchB_sound (by decide) row192_fields
theorem row192_source : sourceKey 192 ∈ geometry.profile (sourceOwner 192) := by decide +kernel
theorem row192_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 168 key1).FastValid geometry rowPose192 := by decide +kernel
theorem row192_illegal : ¬ geometry.LegalContact rowPose192 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row192_reject_checked)
theorem row192_classified : RowClassified 192 := by
  intro p generated legal
  have he : rowPose192 = p := Option.some.inj (row192_generated.symm.trans generated)
  subst p
  exact (row192_illegal legal).elim

def rowPose193 : Pose 7 := ⟨perm24, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row193_fields : pairFieldsMatchB 188160 facet0 facet169 key0 key193 rowPose193 = true := by decide +kernel
theorem row193_generated : rootPair 193 = some rowPose193 :=
  pairFieldsMatchB_sound (by decide) row193_fields
theorem row193_source : sourceKey 193 ∈ geometry.profile (sourceOwner 193) := by decide +kernel
theorem row193_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 169 key1).FastValid geometry rowPose193 := by decide +kernel
theorem row193_illegal : ¬ geometry.LegalContact rowPose193 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row193_reject_checked)
theorem row193_classified : RowClassified 193 := by
  intro p generated legal
  have he : rowPose193 = p := Option.some.inj (row193_generated.symm.trans generated)
  subst p
  exact (row193_illegal legal).elim

def rowPose194 : Pose 7 := ⟨perm38, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row194_fields : pairFieldsMatchB 188160 facet0 facet170 key0 key194 rowPose194 = true := by decide +kernel
theorem row194_generated : rootPair 194 = some rowPose194 :=
  pairFieldsMatchB_sound (by decide) row194_fields
theorem row194_source : sourceKey 194 ∈ geometry.profile (sourceOwner 194) := by decide +kernel
theorem row194_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 170 key0).FastValid geometry rowPose194 := by decide +kernel
theorem row194_illegal : ¬ geometry.LegalContact rowPose194 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row194_reject_checked)
theorem row194_classified : RowClassified 194 := by
  intro p generated legal
  have he : rowPose194 = p := Option.some.inj (row194_generated.symm.trans generated)
  subst p
  exact (row194_illegal legal).elim

def rowPose195 : Pose 7 := ⟨perm56, ![false, true, true, false, true, false, false], ![-2, 1, 2, 0, 1, 0, 0]⟩
theorem row195_fields : pairFieldsMatchB 188160 facet0 facet171 key0 key195 rowPose195 = true := by decide +kernel
theorem row195_generated : rootPair 195 = some rowPose195 :=
  pairFieldsMatchB_sound (by decide) row195_fields
theorem row195_source : sourceKey 195 ∈ geometry.profile (sourceOwner 195) := by decide +kernel
theorem row195_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 171 key1).FastValid geometry rowPose195 := by decide +kernel
theorem row195_illegal : ¬ geometry.LegalContact rowPose195 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row195_reject_checked)
theorem row195_classified : RowClassified 195 := by
  intro p generated legal
  have he : rowPose195 = p := Option.some.inj (row195_generated.symm.trans generated)
  subst p
  exact (row195_illegal legal).elim

def rowPose196 : Pose 7 := ⟨perm69, ![true, false, true, false, false, true, true], ![0, -1, 2, 0, 0, 1, 1]⟩
theorem row196_fields : pairFieldsMatchB 188160 facet0 facet172 key0 key196 rowPose196 = true := by decide +kernel
theorem row196_generated : rootPair 196 = some rowPose196 :=
  pairFieldsMatchB_sound (by decide) row196_fields
theorem row196_source : sourceKey 196 ∈ geometry.profile (sourceOwner 196) := by decide +kernel
theorem row196_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 172 key0).FastValid geometry rowPose196 := by decide +kernel
theorem row196_illegal : ¬ geometry.LegalContact rowPose196 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row196_reject_checked)
theorem row196_classified : RowClassified 196 := by
  intro p generated legal
  have he : rowPose196 = p := Option.some.inj (row196_generated.symm.trans generated)
  subst p
  exact (row196_illegal legal).elim

def rowPose197 : Pose 7 := ⟨perm90, ![true, true, false, false, false, false, true], ![0, 1, 0, 0, -1, -1, 1]⟩
theorem row197_fields : pairFieldsMatchB 188160 facet0 facet173 key0 key197 rowPose197 = true := by decide +kernel
theorem row197_generated : rootPair 197 = some rowPose197 :=
  pairFieldsMatchB_sound (by decide) row197_fields
theorem row197_source : sourceKey 197 ∈ geometry.profile (sourceOwner 197) := by decide +kernel
theorem row197_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 173 key0).FastValid geometry rowPose197 := by decide +kernel
theorem row197_illegal : ¬ geometry.LegalContact rowPose197 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row197_reject_checked)
theorem row197_classified : RowClassified 197 := by
  intro p generated legal
  have he : rowPose197 = p := Option.some.inj (row197_generated.symm.trans generated)
  subst p
  exact (row197_illegal legal).elim

def rowPose198 : Pose 7 := ⟨perm96, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row198_fields : pairFieldsMatchB 188160 facet0 facet174 key0 key198 rowPose198 = true := by decide +kernel
theorem row198_generated : rootPair 198 = some rowPose198 :=
  pairFieldsMatchB_sound (by decide) row198_fields
theorem row198_source : sourceKey 198 ∈ geometry.profile (sourceOwner 198) := by decide +kernel
theorem row198_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 174 key0).FastValid geometry rowPose198 := by decide +kernel
theorem row198_illegal : ¬ geometry.LegalContact rowPose198 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row198_reject_checked)
theorem row198_classified : RowClassified 198 := by
  intro p generated legal
  have he : rowPose198 = p := Option.some.inj (row198_generated.symm.trans generated)
  subst p
  exact (row198_illegal legal).elim

def rowPose199 : Pose 7 := ⟨perm111, ![true, false, false, true, true, false, false], ![0, 0, 0, 2, 2, 0, 0]⟩
theorem row199_fields : pairFieldsMatchB 188160 facet0 facet174 key0 key199 rowPose199 = true := by decide +kernel
theorem row199_generated : rootPair 199 = some rowPose199 :=
  pairFieldsMatchB_sound (by decide) row199_fields
theorem row199_source : sourceKey 199 ∈ geometry.profile (sourceOwner 199) := by decide +kernel
theorem row199_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 623 key8).FastValid geometry rowPose199 := by decide +kernel
theorem row199_illegal : ¬ geometry.LegalContact rowPose199 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row199_reject_checked)
theorem row199_classified : RowClassified 199 := by
  intro p generated legal
  have he : rowPose199 = p := Option.some.inj (row199_generated.symm.trans generated)
  subst p
  exact (row199_illegal legal).elim

def rowPose200 : Pose 7 := ⟨perm15, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row200_fields : pairFieldsMatchB 188160 facet0 facet175 key0 key200 rowPose200 = true := by decide +kernel
theorem row200_generated : rootPair 200 = some rowPose200 :=
  pairFieldsMatchB_sound (by decide) row200_fields
theorem row200_source : sourceKey 200 ∈ geometry.profile (sourceOwner 200) := by decide +kernel
theorem row200_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 175 key0).FastValid geometry rowPose200 := by decide +kernel
theorem row200_illegal : ¬ geometry.LegalContact rowPose200 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row200_reject_checked)
theorem row200_classified : RowClassified 200 := by
  intro p generated legal
  have he : rowPose200 = p := Option.some.inj (row200_generated.symm.trans generated)
  subst p
  exact (row200_illegal legal).elim

def rowPose201 : Pose 7 := ⟨perm24, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row201_fields : pairFieldsMatchB 188160 facet0 facet176 key0 key201 rowPose201 = true := by decide +kernel
theorem row201_generated : rootPair 201 = some rowPose201 :=
  pairFieldsMatchB_sound (by decide) row201_fields
theorem row201_source : sourceKey 201 ∈ geometry.profile (sourceOwner 201) := by decide +kernel
theorem row201_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 176 key0).FastValid geometry rowPose201 := by decide +kernel
theorem row201_illegal : ¬ geometry.LegalContact rowPose201 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row201_reject_checked)
theorem row201_classified : RowClassified 201 := by
  intro p generated legal
  have he : rowPose201 = p := Option.some.inj (row201_generated.symm.trans generated)
  subst p
  exact (row201_illegal legal).elim

def rowPose202 : Pose 7 := ⟨perm38, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row202_fields : pairFieldsMatchB 188160 facet0 facet177 key0 key202 rowPose202 = true := by decide +kernel
theorem row202_generated : rootPair 202 = some rowPose202 :=
  pairFieldsMatchB_sound (by decide) row202_fields
theorem row202_source : sourceKey 202 ∈ geometry.profile (sourceOwner 202) := by decide +kernel
theorem row202_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 177 key1).FastValid geometry rowPose202 := by decide +kernel
theorem row202_illegal : ¬ geometry.LegalContact rowPose202 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row202_reject_checked)
theorem row202_classified : RowClassified 202 := by
  intro p generated legal
  have he : rowPose202 = p := Option.some.inj (row202_generated.symm.trans generated)
  subst p
  exact (row202_illegal legal).elim

def rowPose203 : Pose 7 := ⟨perm56, ![false, true, true, false, true, true, false], ![-2, 1, 2, 0, 1, 2, 0]⟩
theorem row203_fields : pairFieldsMatchB 188160 facet0 facet178 key0 key203 rowPose203 = true := by decide +kernel
theorem row203_generated : rootPair 203 = some rowPose203 :=
  pairFieldsMatchB_sound (by decide) row203_fields
theorem row203_source : sourceKey 203 ∈ geometry.profile (sourceOwner 203) := by decide +kernel
theorem row203_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 178 key0).FastValid geometry rowPose203 := by decide +kernel
theorem row203_illegal : ¬ geometry.LegalContact rowPose203 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row203_reject_checked)
theorem row203_classified : RowClassified 203 := by
  intro p generated legal
  have he : rowPose203 = p := Option.some.inj (row203_generated.symm.trans generated)
  subst p
  exact (row203_illegal legal).elim

def rowPose204 : Pose 7 := ⟨perm69, ![true, false, true, false, false, false, true], ![0, -1, 2, 0, 0, -1, 1]⟩
theorem row204_fields : pairFieldsMatchB 188160 facet0 facet179 key0 key204 rowPose204 = true := by decide +kernel
theorem row204_generated : rootPair 204 = some rowPose204 :=
  pairFieldsMatchB_sound (by decide) row204_fields
theorem row204_source : sourceKey 204 ∈ geometry.profile (sourceOwner 204) := by decide +kernel
theorem row204_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 179 key1).FastValid geometry rowPose204 := by decide +kernel
theorem row204_illegal : ¬ geometry.LegalContact rowPose204 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row204_reject_checked)
theorem row204_classified : RowClassified 204 := by
  intro p generated legal
  have he : rowPose204 = p := Option.some.inj (row204_generated.symm.trans generated)
  subst p
  exact (row204_illegal legal).elim

def rowPose205 : Pose 7 := ⟨perm90, ![true, false, false, false, false, false, true], ![0, -1, 0, 0, -1, -1, 1]⟩
theorem row205_fields : pairFieldsMatchB 188160 facet0 facet180 key0 key205 rowPose205 = true := by decide +kernel
theorem row205_generated : rootPair 205 = some rowPose205 :=
  pairFieldsMatchB_sound (by decide) row205_fields
theorem row205_source : sourceKey 205 ∈ geometry.profile (sourceOwner 205) := by decide +kernel
theorem row205_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 180 key1).FastValid geometry rowPose205 := by decide +kernel
theorem row205_illegal : ¬ geometry.LegalContact rowPose205 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row205_reject_checked)
theorem row205_classified : RowClassified 205 := by
  intro p generated legal
  have he : rowPose205 = p := Option.some.inj (row205_generated.symm.trans generated)
  subst p
  exact (row205_illegal legal).elim

def rowPose206 : Pose 7 := ⟨perm96, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row206_fields : pairFieldsMatchB 188160 facet0 facet181 key0 key206 rowPose206 = true := by decide +kernel
theorem row206_generated : rootPair 206 = some rowPose206 :=
  pairFieldsMatchB_sound (by decide) row206_fields
theorem row206_source : sourceKey 206 ∈ geometry.profile (sourceOwner 206) := by decide +kernel
theorem row206_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 195 key8).FastValid geometry rowPose206 := by decide +kernel
theorem row206_illegal : ¬ geometry.LegalContact rowPose206 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row206_reject_checked)
theorem row206_classified : RowClassified 206 := by
  intro p generated legal
  have he : rowPose206 = p := Option.some.inj (row206_generated.symm.trans generated)
  subst p
  exact (row206_illegal legal).elim

def rowPose207 : Pose 7 := ⟨perm111, ![false, false, false, true, true, false, false], ![-2, 0, 0, 2, 2, 0, 0]⟩
theorem row207_fields : pairFieldsMatchB 188160 facet0 facet181 key0 key207 rowPose207 = true := by decide +kernel
theorem row207_generated : rootPair 207 = some rowPose207 :=
  pairFieldsMatchB_sound (by decide) row207_fields
theorem row207_source : sourceKey 207 ∈ geometry.profile (sourceOwner 207) := by decide +kernel
theorem row207_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 181 key0).FastValid geometry rowPose207 := by decide +kernel
theorem row207_illegal : ¬ geometry.LegalContact rowPose207 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row207_reject_checked)
theorem row207_classified : RowClassified 207 := by
  intro p generated legal
  have he : rowPose207 = p := Option.some.inj (row207_generated.symm.trans generated)
  subst p
  exact (row207_illegal legal).elim

def rowPose208 : Pose 7 := ⟨perm0, ![true, true, true, true, true, false, true], ![0, 1, 2, 2, 1, -1, 1]⟩
theorem row208_fields : pairFieldsMatchB 188160 facet0 facet182 key0 key208 rowPose208 = true := by decide +kernel
theorem row208_generated : rootPair 208 = some rowPose208 :=
  pairFieldsMatchB_sound (by decide) row208_fields
theorem row208_source : sourceKey 208 ∈ geometry.profile (sourceOwner 208) := by decide +kernel
theorem row208_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 182 key1).FastValid geometry rowPose208 := by decide +kernel
theorem row208_illegal : ¬ geometry.LegalContact rowPose208 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row208_reject_checked)
theorem row208_classified : RowClassified 208 := by
  intro p generated legal
  have he : rowPose208 = p := Option.some.inj (row208_generated.symm.trans generated)
  subst p
  exact (row208_illegal legal).elim

def rowPose209 : Pose 7 := ⟨perm21, ![true, false, false, true, false, true, true], ![0, 0, 0, 2, 0, 2, 2]⟩
theorem row209_fields : pairFieldsMatchB 188160 facet0 facet183 key0 key209 rowPose209 = true := by decide +kernel
theorem row209_generated : rootPair 209 = some rowPose209 :=
  pairFieldsMatchB_sound (by decide) row209_fields
theorem row209_source : sourceKey 209 ∈ geometry.profile (sourceOwner 209) := by decide +kernel
theorem row209_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 183 key0).FastValid geometry rowPose209 := by decide +kernel
theorem row209_illegal : ¬ geometry.LegalContact rowPose209 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row209_reject_checked)
theorem row209_classified : RowClassified 209 := by
  intro p generated legal
  have he : rowPose209 = p := Option.some.inj (row209_generated.symm.trans generated)
  subst p
  exact (row209_illegal legal).elim

def rowPose210 : Pose 7 := ⟨perm24, ![true, true, true, false, true, false, false], ![0, 2, 2, 0, 2, 0, 0]⟩
theorem row210_fields : pairFieldsMatchB 188160 facet0 facet183 key0 key210 rowPose210 = true := by decide +kernel
theorem row210_generated : rootPair 210 = some rowPose210 :=
  pairFieldsMatchB_sound (by decide) row210_fields
theorem row210_source : sourceKey 210 ∈ geometry.profile (sourceOwner 210) := by decide +kernel
theorem row210_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 632 key8).FastValid geometry rowPose210 := by decide +kernel
theorem row210_illegal : ¬ geometry.LegalContact rowPose210 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row210_reject_checked)
theorem row210_classified : RowClassified 210 := by
  intro p generated legal
  have he : rowPose210 = p := Option.some.inj (row210_generated.symm.trans generated)
  subst p
  exact (row210_illegal legal).elim

def rowPose211 : Pose 7 := ⟨perm37, ![false, true, false, false, false, true, false], ![-2, 1, 0, 0, -1, 1, -1]⟩
theorem row211_fields : pairFieldsMatchB 188160 facet0 facet184 key0 key211 rowPose211 = true := by decide +kernel
theorem row211_generated : rootPair 211 = some rowPose211 :=
  pairFieldsMatchB_sound (by decide) row211_fields
theorem row211_source : sourceKey 211 ∈ geometry.profile (sourceOwner 211) := by decide +kernel
theorem row211_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 184 key0).FastValid geometry rowPose211 := by decide +kernel
theorem row211_illegal : ¬ geometry.LegalContact rowPose211 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row211_reject_checked)
theorem row211_classified : RowClassified 211 := by
  intro p generated legal
  have he : rowPose211 = p := Option.some.inj (row211_generated.symm.trans generated)
  subst p
  exact (row211_illegal legal).elim

def rowPose212 : Pose 7 := ⟨perm58, ![false, true, true, false, false, true, false], ![-2, 1, 2, 0, 0, 1, -1]⟩
theorem row212_fields : pairFieldsMatchB 188160 facet0 facet185 key0 key212 rowPose212 = true := by decide +kernel
theorem row212_generated : rootPair 212 = some rowPose212 :=
  pairFieldsMatchB_sound (by decide) row212_fields
theorem row212_source : sourceKey 212 ∈ geometry.profile (sourceOwner 212) := by decide +kernel
theorem row212_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 185 key0).FastValid geometry rowPose212 := by decide +kernel
theorem row212_illegal : ¬ geometry.LegalContact rowPose212 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row212_reject_checked)
theorem row212_classified : RowClassified 212 := by
  intro p generated legal
  have he : rowPose212 = p := Option.some.inj (row212_generated.symm.trans generated)
  subst p
  exact (row212_illegal legal).elim

def rowPose213 : Pose 7 := ⟨perm71, ![true, false, true, false, true, false, true], ![0, -1, 2, 0, 1, 0, 2]⟩
theorem row213_fields : pairFieldsMatchB 188160 facet0 facet186 key0 key213 rowPose213 = true := by decide +kernel
theorem row213_generated : rootPair 213 = some rowPose213 :=
  pairFieldsMatchB_sound (by decide) row213_fields
theorem row213_source : sourceKey 213 ∈ geometry.profile (sourceOwner 213) := by decide +kernel
theorem row213_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 186 key1).FastValid geometry rowPose213 := by decide +kernel
theorem row213_illegal : ¬ geometry.LegalContact rowPose213 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row213_reject_checked)
theorem row213_classified : RowClassified 213 := by
  intro p generated legal
  have he : rowPose213 = p := Option.some.inj (row213_generated.symm.trans generated)
  subst p
  exact (row213_illegal legal).elim

def rowPose214 : Pose 7 := ⟨perm95, ![false, true, false, true, false, false, false], ![-2, 1, 0, 2, -1, 0, 0]⟩
theorem row214_fields : pairFieldsMatchB 188160 facet0 facet187 key0 key214 rowPose214 = true := by decide +kernel
theorem row214_generated : rootPair 214 = some rowPose214 :=
  pairFieldsMatchB_sound (by decide) row214_fields
theorem row214_source : sourceKey 214 ∈ geometry.profile (sourceOwner 214) := by decide +kernel
theorem row214_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 187 key0).FastValid geometry rowPose214 := by decide +kernel
theorem row214_illegal : ¬ geometry.LegalContact rowPose214 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row214_reject_checked)
theorem row214_classified : RowClassified 214 := by
  intro p generated legal
  have he : rowPose214 = p := Option.some.inj (row214_generated.symm.trans generated)
  subst p
  exact (row214_illegal legal).elim

def rowPose215 : Pose 7 := ⟨perm111, ![true, false, false, true, true, true, true], ![0, -1, 0, 2, 2, 1, 1]⟩
theorem row215_fields : pairFieldsMatchB 188160 facet0 facet188 key0 key215 rowPose215 = true := by decide +kernel
theorem row215_generated : rootPair 215 = some rowPose215 :=
  pairFieldsMatchB_sound (by decide) row215_fields
theorem row215_source : sourceKey 215 ∈ geometry.profile (sourceOwner 215) := by decide +kernel
theorem row215_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 188 key1).FastValid geometry rowPose215 := by decide +kernel
theorem row215_illegal : ¬ geometry.LegalContact rowPose215 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row215_reject_checked)
theorem row215_classified : RowClassified 215 := by
  intro p generated legal
  have he : rowPose215 = p := Option.some.inj (row215_generated.symm.trans generated)
  subst p
  exact (row215_illegal legal).elim

def rowPose216 : Pose 7 := ⟨perm10, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row216_fields : pairFieldsMatchB 188160 facet0 facet189 key0 key216 rowPose216 = true := by decide +kernel
theorem row216_generated : rootPair 216 = some rowPose216 :=
  pairFieldsMatchB_sound (by decide) row216_fields
theorem row216_source : sourceKey 216 ∈ geometry.profile (sourceOwner 216) := by decide +kernel
theorem row216_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 189 key0).FastValid geometry rowPose216 := by decide +kernel
theorem row216_illegal : ¬ geometry.LegalContact rowPose216 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row216_reject_checked)
theorem row216_classified : RowClassified 216 := by
  intro p generated legal
  have he : rowPose216 = p := Option.some.inj (row216_generated.symm.trans generated)
  subst p
  exact (row216_illegal legal).elim

def rowPose217 : Pose 7 := ⟨perm22, ![true, false, false, true, false, false, true], ![0, -1, 0, 2, -1, 0, 2]⟩
theorem row217_fields : pairFieldsMatchB 188160 facet0 facet190 key0 key217 rowPose217 = true := by decide +kernel
theorem row217_generated : rootPair 217 = some rowPose217 :=
  pairFieldsMatchB_sound (by decide) row217_fields
theorem row217_source : sourceKey 217 ∈ geometry.profile (sourceOwner 217) := by decide +kernel
theorem row217_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 190 key1).FastValid geometry rowPose217 := by decide +kernel
theorem row217_illegal : ¬ geometry.LegalContact rowPose217 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row217_reject_checked)
theorem row217_classified : RowClassified 217 := by
  intro p generated legal
  have he : rowPose217 = p := Option.some.inj (row217_generated.symm.trans generated)
  subst p
  exact (row217_illegal legal).elim

def rowPose218 : Pose 7 := ⟨perm37, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row218_fields : pairFieldsMatchB 188160 facet0 facet191 key0 key218 rowPose218 = true := by decide +kernel
theorem row218_generated : rootPair 218 = some rowPose218 :=
  pairFieldsMatchB_sound (by decide) row218_fields
theorem row218_source : sourceKey 218 ∈ geometry.profile (sourceOwner 218) := by decide +kernel
theorem row218_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 191 key0).FastValid geometry rowPose218 := by decide +kernel
theorem row218_illegal : ¬ geometry.LegalContact rowPose218 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row218_reject_checked)
theorem row218_classified : RowClassified 218 := by
  intro p generated legal
  have he : rowPose218 = p := Option.some.inj (row218_generated.symm.trans generated)
  subst p
  exact (row218_illegal legal).elim

def rowPose219 : Pose 7 := ⟨perm58, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row219_fields : pairFieldsMatchB 188160 facet0 facet192 key0 key219 rowPose219 = true := by decide +kernel
theorem row219_generated : rootPair 219 = some rowPose219 :=
  pairFieldsMatchB_sound (by decide) row219_fields
theorem row219_source : sourceKey 219 ∈ geometry.profile (sourceOwner 219) := by decide +kernel
theorem row219_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 192 key0).FastValid geometry rowPose219 := by decide +kernel
theorem row219_illegal : ¬ geometry.LegalContact rowPose219 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row219_reject_checked)
theorem row219_classified : RowClassified 219 := by
  intro p generated legal
  have he : rowPose219 = p := Option.some.inj (row219_generated.symm.trans generated)
  subst p
  exact (row219_illegal legal).elim

def rowPose220 : Pose 7 := ⟨perm74, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row220_fields : pairFieldsMatchB 188160 facet0 facet193 key0 key220 rowPose220 = true := by decide +kernel
theorem row220_generated : rootPair 220 = some rowPose220 :=
  pairFieldsMatchB_sound (by decide) row220_fields
theorem row220_source : sourceKey 220 ∈ geometry.profile (sourceOwner 220) := by decide +kernel
theorem row220_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 193 key0).FastValid geometry rowPose220 := by decide +kernel
theorem row220_illegal : ¬ geometry.LegalContact rowPose220 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row220_reject_checked)
theorem row220_classified : RowClassified 220 := by
  intro p generated legal
  have he : rowPose220 = p := Option.some.inj (row220_generated.symm.trans generated)
  subst p
  exact (row220_illegal legal).elim

def rowPose221 : Pose 7 := ⟨perm69, ![true, true, true, false, false, true, true], ![0, 2, 2, 0, 0, 2, 2]⟩
theorem row221_fields : pairFieldsMatchB 188160 facet0 facet193 key0 key221 rowPose221 = true := by decide +kernel
theorem row221_generated : rootPair 221 = some rowPose221 :=
  pairFieldsMatchB_sound (by decide) row221_fields
theorem row221_source : sourceKey 221 ∈ geometry.profile (sourceOwner 221) := by decide +kernel
theorem row221_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 7 179 key8).FastValid geometry rowPose221 := by decide +kernel
theorem row221_illegal : ¬ geometry.LegalContact rowPose221 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row221_reject_checked)
theorem row221_classified : RowClassified 221 := by
  intro p generated legal
  have he : rowPose221 = p := Option.some.inj (row221_generated.symm.trans generated)
  subst p
  exact (row221_illegal legal).elim

def rowPose222 : Pose 7 := ⟨perm87, ![false, true, true, true, true, true, false], ![-2, 1, 2, 2, 1, 1, -1]⟩
theorem row222_fields : pairFieldsMatchB 188160 facet0 facet194 key0 key222 rowPose222 = true := by decide +kernel
theorem row222_generated : rootPair 222 = some rowPose222 :=
  pairFieldsMatchB_sound (by decide) row222_fields
theorem row222_source : sourceKey 222 ∈ geometry.profile (sourceOwner 222) := by decide +kernel
theorem row222_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 194 key1).FastValid geometry rowPose222 := by decide +kernel
theorem row222_illegal : ¬ geometry.LegalContact rowPose222 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row222_reject_checked)
theorem row222_classified : RowClassified 222 := by
  intro p generated legal
  have he : rowPose222 = p := Option.some.inj (row222_generated.symm.trans generated)
  subst p
  exact (row222_illegal legal).elim

def rowPose223 : Pose 7 := ⟨perm96, ![false, true, false, true, true, true, false], ![-2, 1, 0, 2, 2, 1, -1]⟩
theorem row223_fields : pairFieldsMatchB 188160 facet0 facet195 key0 key223 rowPose223 = true := by decide +kernel
theorem row223_generated : rootPair 223 = some rowPose223 :=
  pairFieldsMatchB_sound (by decide) row223_fields
theorem row223_source : sourceKey 223 ∈ geometry.profile (sourceOwner 223) := by decide +kernel
theorem row223_reject_checked : (show IndexedRejection 7 896 from .unmatchedRoot 0 195 key1).FastValid geometry rowPose223 := by decide +kernel
theorem row223_illegal : ¬ geometry.LegalContact rowPose223 :=
  IndexedRejection.sound (IndexedRejection.fastValid_valid cells_eq row223_reject_checked)
theorem row223_classified : RowClassified 223 := by
  intro p generated legal
  have he : rowPose223 = p := Option.some.inj (row223_generated.symm.trans generated)
  subst p
  exact (row223_illegal legal).elim

theorem chunk06_classified (i : Fin 32) : RowClassified ⟨192 + i.val, by omega⟩ := by
  fin_cases i
  · exact row192_classified
  · exact row193_classified
  · exact row194_classified
  · exact row195_classified
  · exact row196_classified
  · exact row197_classified
  · exact row198_classified
  · exact row199_classified
  · exact row200_classified
  · exact row201_classified
  · exact row202_classified
  · exact row203_classified
  · exact row204_classified
  · exact row205_classified
  · exact row206_classified
  · exact row207_classified
  · exact row208_classified
  · exact row209_classified
  · exact row210_classified
  · exact row211_classified
  · exact row212_classified
  · exact row213_classified
  · exact row214_classified
  · exact row215_classified
  · exact row216_classified
  · exact row217_classified
  · exact row218_classified
  · exact row219_classified
  · exact row220_classified
  · exact row221_classified
  · exact row222_classified
  · exact row223_classified

theorem chunk06_source (i : Fin 32) : sourceKey ⟨192 + i.val, by omega⟩ ∈ geometry.profile (sourceOwner ⟨192 + i.val, by omega⟩) := by
  fin_cases i
  · exact row192_source
  · exact row193_source
  · exact row194_source
  · exact row195_source
  · exact row196_source
  · exact row197_source
  · exact row198_source
  · exact row199_source
  · exact row200_source
  · exact row201_source
  · exact row202_source
  · exact row203_source
  · exact row204_source
  · exact row205_source
  · exact row206_source
  · exact row207_source
  · exact row208_source
  · exact row209_source
  · exact row210_source
  · exact row211_source
  · exact row212_source
  · exact row213_source
  · exact row214_source
  · exact row215_source
  · exact row216_source
  · exact row217_source
  · exact row218_source
  · exact row219_source
  · exact row220_source
  · exact row221_source
  · exact row222_source
  · exact row223_source

#print axioms chunk06_classified
end SparseMonotiles.Contact.RootZeroPilot7
