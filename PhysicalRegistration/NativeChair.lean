module

public import PhysicalRegistration.KeyHypograph
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Nat.Prime.Infinite

@[expose] public section

/-!
# The literal finite native keyed chair

This file implements the carrier and rational native geometry of sections 1–2
of `REGISTRATION_THEOREM.md`. The ambient space really is Euclidean `(m+1)`-space.
The supplied integer coefficients are NOT claimed to come from the prescribed
contact graph: constructing that graph and its component assignment is separate.
Likewise, these definitions do not assert tube separation, ball topology, or
arbitrary-congruence registration.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set

noncomputable section

/-- `m` tangent coordinates and one normal coordinate. -/
abbrev Space (m : ℕ) := EuclideanSpace ℝ (Fin (m + 1))

/-- The occupied binary cells: all masks except the all-true mask. -/
def Cell (m : ℕ) := {a : Fin (m + 1) → Bool // a ≠ fun _ => true}

instance (m : ℕ) : Fintype (Cell m) := inferInstanceAs (Fintype {_a // _})
instance (m : ℕ) : DecidableEq (Cell m) := inferInstanceAs (DecidableEq {_a // _})

/-- The actual coordinate of a binary cell's lower corner. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- A closed, axis-parallel unit cell in the actual Euclidean ambient space. -/
def unitCell {m : ℕ} (a : Cell m) : Set (Space m) :=
  {x | ∀ i, bit (a.val i) ≤ x i ∧ x i ≤ bit (a.val i) + 1}

/-- `P_(m+1)`, the union of the occupied closed unit cells. -/
def carrier (m : ℕ) : Set (Space m) := ⋃ a : Cell m, unitCell a

/-- Each occupied cell contributes its one outer facet in each coordinate
 direction. The remaining `m+1` facets face the missing all-true cell. -/
abbrev Facet (m : ℕ) := (Cell m × Fin (m + 1)) ⊕ Fin (m + 1)

/-- The tangent key frame is a permutation with independent column signs.
 `true` means the positive sign. Its action sends column `j` to
 `sign(j) e_(perm(j))`. -/
abbrev Frame (m : ℕ) := Equiv.Perm (Fin m) × (Fin m → Bool)

/-- Native sites are not quotiented by tangent frames. -/
abbrev Site (m : ℕ) := Facet m × Frame m

theorem card_cell (m : ℕ) : Fintype.card (Cell m) = 2 ^ (m + 1) - 1 := by
  rw [show Fintype.card (Cell m) =
      Fintype.card {a : Fin (m + 1) → Bool // ¬a = fun _ => true} from
    Fintype.card_congr (Equiv.refl _)]
  rw [Fintype.card_subtype_compl (fun a : Fin (m + 1) → Bool => a = fun _ => true)]
  simp

theorem card_facet (m : ℕ) : Fintype.card (Facet m) = (m + 1) * 2 ^ (m + 1) := by
  simp only [Facet, Fintype.card_sum, Fintype.card_prod, card_cell, Fintype.card_fin]
  have hpow : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by decide)
  calc
    (2 ^ (m + 1) - 1) * (m + 1) + (m + 1) =
        ((2 ^ (m + 1) - 1) + 1) * (m + 1) := by ring
    _ = (m + 1) * 2 ^ (m + 1) := by rw [Nat.sub_add_cancel hpow]; ring

theorem card_frame (m : ℕ) : Fintype.card (Frame m) = m.factorial * 2 ^ m := by
  simp [Frame, Fintype.card_perm]

theorem card_site (m : ℕ) :
    Fintype.card (Site m) = (m + 1) * 2 ^ (m + 1) * (2 ^ m * m.factorial) := by
  rw [Fintype.card_prod, card_facet, card_frame]
  ring

def sign (b : Bool) : ℝ := if b then 1 else -1

def normalIndex {m : ℕ} : Facet m → Fin (m + 1)
  | .inl (_, i) => i
  | .inr i => i

def normalSign {m : ℕ} : Facet m → ℝ
  | .inl (a, i) => sign (a.val i)
  | .inr _ => 1

/-- Outer planes have coordinate 0 or 2. Inner, reentrant planes have
 coordinate 1 and their material-outward normal points toward the missing cell. -/
def facetCenter {m : ℕ} (f : Facet m) : Space m :=
  WithLp.toLp 2 (fun k => match f with
    | .inl (a, i) => if k = i then (if a.val i then 2 else 0)
        else bit (a.val k) + 1 / 2
    | .inr i => if k = i then 1 else 3 / 2)

def outward {m : ℕ} (f : Facet m) : Space m :=
  normalSign f • EuclideanSpace.single (normalIndex f) 1

/-- The increasing ambient-coordinate order with the normal index omitted. -/
def tangentAxis {m : ℕ} (f : Facet m) (j : Fin m) : Space m :=
  EuclideanSpace.single ((normalIndex f).succAbove j) 1

/-- Column `j` of the keyed native tangent frame `I_f A_q`. -/
def siteAxis {m : ℕ} (u : Site m) (j : Fin m) : Space m :=
  sign (u.2.2 j) • tangentAxis u.1 (u.2.1 j)

/-- The exact free-orbit seed, indexed from zero in Lean. -/
def q0 {m : ℕ} (j : Fin m) : ℝ :=
  ((j.val : ℝ) + 1) / (4 * ((m : ℝ) + 1))

def siteOffset {m : ℕ} (u : Site m) : Space m :=
  ∑ j : Fin m, q0 j • siteAxis u j

def siteCenter {m : ℕ} (u : Site m) : Space m :=
  facetCenter u.1 + siteOffset u

def delta (m : ℕ) : ℝ := 1 / (16 * ((m : ℝ) + 1))
def eta (m : ℕ) : ℝ := 1 / (128 * ((m : ℝ) + 1))
def rho (m : ℕ) : ℝ := 1 / (32 * ((m : ℝ) + 1))

/-- The least prime strictly above a natural number. -/
def nextPrime (n : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (n + 1))

theorem nextPrime_spec (n : ℕ) : n < nextPrime n ∧ Nat.Prime (nextPrime n) := by
  have h := Nat.find_spec (Nat.exists_infinite_primes (n + 1))
  exact ⟨h.1, h.2⟩

theorem nextPrime_min (n p : ℕ) (hn : n < p) (hp : Nat.Prime p) :
    nextPrime n ≤ p := Nat.find_min' _ ⟨hn, hp⟩

/-- Consecutive primes strictly above `J`, in increasing order. -/
def keyPrime (J : ℕ) : ℕ → ℕ
  | 0 => nextPrime J
  | n + 1 => nextPrime (keyPrime J n)

def pMinus {m : ℕ} (J : ℕ) (j : Fin m) : ℝ := keyPrime J (2 * j.val)
def pPlus {m : ℕ} (J : ℕ) (j : Fin m) : ℝ := keyPrime J (2 * j.val + 1)
def pMax (m J : ℕ) : ℕ := keyPrime J (2 * m - 1)

/-- The manuscript's exact least-prime denominator. -/
def denominator (m J : ℕ) : ℕ := nextPrime (32 * (m + 1) * J * pMax m J)

theorem keyPrime_prime (J n : ℕ) : Nat.Prime (keyPrime J n) := by
  cases n with
  | zero => exact (nextPrime_spec J).2
  | succ n => exact (nextPrime_spec (keyPrime J n)).2

theorem keyPrime_strictMono (J : ℕ) : StrictMono (keyPrime J) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (nextPrime_spec (keyPrime J n)).1

theorem keyPrime_gt (J n : ℕ) : J < keyPrime J n :=
  (nextPrime_spec J).1.trans_le ((keyPrime_strictMono J).monotone (Nat.zero_le n))

theorem pMinus_pos {m : ℕ} (J : ℕ) (j : Fin m) : 0 < pMinus J j := by
  unfold pMinus
  exact_mod_cast (keyPrime_prime J (2 * j.val)).pos

theorem pPlus_pos {m : ℕ} (J : ℕ) (j : Fin m) : 0 < pPlus J j := by
  unfold pPlus
  exact_mod_cast (keyPrime_prime J (2 * j.val + 1)).pos

theorem pMinus_le_pMax {m : ℕ} (J : ℕ) (j : Fin m) :
    pMinus J j ≤ (pMax m J : ℝ) := by
  have hj : 2 * j.val ≤ 2 * m - 1 := by omega
  unfold pMinus pMax
  exact_mod_cast (keyPrime_strictMono J).monotone hj

theorem pPlus_le_pMax {m : ℕ} (J : ℕ) (j : Fin m) :
    pPlus J j ≤ (pMax m J : ℝ) := by
  have hj : 2 * j.val + 1 ≤ 2 * m - 1 := by omega
  unfold pPlus pMax
  exact_mod_cast (keyPrime_strictMono J).monotone hj

theorem denominator_prime (m J : ℕ) : Nat.Prime (denominator m J) :=
  (nextPrime_spec _).2

theorem denominator_gt (m J : ℕ) :
    32 * (m + 1) * J * pMax m J < denominator m J := (nextPrime_spec _).1

/-- Explicit coefficient input. No contact-graph, chirality, or component
 theorem is hidden in this structure. The bound is in the real field to feed
 the checked analytic estimates without an implicit cast convention. -/
structure Coefficients (m J : ℕ) where
  value : Site m → ℤ
  bound : ∀ u, |(value u : ℝ)| ≤ (J : ℝ)
  nonzero : ∀ u, value u ≠ 0

/-- Outward normal coordinate centered at a native site. -/
def normalCoord {m : ℕ} (u : Site m) (x : Space m) : ℝ :=
  ⟪outward u.1, x - siteCenter u⟫_ℝ

/-- The coordinate in column `j` of the keyed native tangent frame. -/
def tangentCoord {m : ℕ} (u : Site m) (x : Space m) (j : Fin m) : ℝ :=
  ⟪siteAxis u j, x - siteCenter u⟫_ℝ

/-- The exact asymmetric closed footprint `K`, in keyed coordinates. -/
def footprint (m J : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {v | ∀ j, -eta m / pMinus J j ≤ v j ∧ v j ≤ eta m / pPlus J j}

/-- The actual closed ambient tube, with normal half-width `rho`. -/
def closedTube {m : ℕ} (J : ℕ) (u : Site m) : Set (Space m) :=
  {x | |normalCoord u x| ≤ rho m ∧
    ∀ j, -eta m / pMinus J j ≤ tangentCoord u x j ∧
      tangentCoord u x j ≤ eta m / pPlus J j}

/-- The exact signed normal graph, expressed using the proved max-min tent. -/
def siteHeight {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (x : Space m) : ℝ :=
  keyHeight (eta m) (a.value u : ℝ) (denominator m J : ℝ)
    (pMinus J) (pPlus J) (siteAxis u) (x - siteCenter u)

/-- Material is on the inward side of the signed graph. -/
def siteHypograph {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) : Set (Space m) :=
  {x | normalCoord u x ≤ siteHeight a u x}

/-- The replacement is restricted to the closed asymmetric tube. -/
def replacementPiece {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) : Set (Space m) :=
  closedTube J u ∩ siteHypograph a u

/-- The literal assembled set. Only tube interiors are removed from the
 carrier, and closed hypograph pieces are inserted. Whether this set is a
 ball and whether different native tubes are disjoint are separate theorems. -/
def body {m J : ℕ} [NeZero m] (a : Coefficients m J) : Set (Space m) :=
  (carrier m \ ⋃ u : Site m, interior (closedTube J u)) ∪
    ⋃ u : Site m, replacementPiece a u

@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]

@[simp] theorem abs_normalSign {m : ℕ} (f : Facet m) : |normalSign f| = 1 := by
  cases f with
  | inl ai => exact abs_sign _
  | inr i => simp [normalSign]

@[simp] theorem outward_unit {m : ℕ} (f : Facet m) : ‖outward f‖ = 1 := by
  simp [outward, norm_smul, Real.norm_eq_abs]

@[simp] theorem siteAxis_unit {m : ℕ} (u : Site m) (j : Fin m) :
    ‖siteAxis u j‖ = 1 := by
  simp [siteAxis, tangentAxis, norm_smul, Real.norm_eq_abs]

@[simp] theorem siteAxis_outward_inner {m : ℕ} (u : Site m) (j : Fin m) :
    ⟪siteAxis u j, outward u.1⟫_ℝ = 0 := by
  simp [siteAxis, tangentAxis, outward, real_inner_smul_left,
    real_inner_smul_right, EuclideanSpace.inner_single_left]

@[simp] theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  cases b <;> norm_num [sign]

/-- The signed permuted tangent columns form an orthonormal family. -/
theorem siteAxis_inner {m : ℕ} (u : Site m) (i j : Fin m) :
    ⟪siteAxis u i, siteAxis u j⟫_ℝ = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp
  · simp [siteAxis, tangentAxis, real_inner_smul_left, real_inner_smul_right,
      EuclideanSpace.inner_single_left, h]

@[simp] theorem outward_siteOffset_inner {m : ℕ} (u : Site m) :
    ⟪outward u.1, siteOffset u⟫_ℝ = 0 := by
  have horth : ∀ j, ⟪outward u.1, siteAxis u j⟫_ℝ = 0 := by
    intro j
    rw [real_inner_comm]
    exact siteAxis_outward_inner u j
  simp [siteOffset, inner_sum, real_inner_smul_right, horth]

@[simp] theorem siteAxis_siteOffset_inner {m : ℕ} (u : Site m) (j : Fin m) :
    ⟪siteAxis u j, siteOffset u⟫_ℝ = q0 j := by
  simp [siteOffset, inner_sum, real_inner_smul_right, siteAxis_inner]

theorem outward_inner_coordinate {m : ℕ} (f : Facet m) (v : Space m) :
    ⟪outward f, v⟫_ℝ = normalSign f * v (normalIndex f) := by
  simp [outward, real_inner_smul_left, EuclideanSpace.inner_single_left]

theorem siteAxis_inner_coordinate {m : ℕ} (u : Site m) (j : Fin m) (v : Space m) :
    ⟪siteAxis u j, v⟫_ℝ =
      sign (u.2.2 j) * v ((normalIndex u.1).succAbove (u.2.1 j)) := by
  simp [siteAxis, tangentAxis, real_inner_smul_left, EuclideanSpace.inner_single_left]

@[simp] theorem siteOffset_normal {m : ℕ} (u : Site m) :
    siteOffset u (normalIndex u.1) = 0 := by
  have h := outward_siteOffset_inner u
  simp only [outward, real_inner_smul_left, EuclideanSpace.inner_single_left,
    map_one, one_mul] at h
  have hn : normalSign u.1 ≠ 0 := by
    intro hz
    have := abs_normalSign u.1
    simp [hz] at this
  exact (mul_eq_zero.mp h).resolve_left hn

theorem siteOffset_tangent {m : ℕ} (u : Site m) (j : Fin m) :
    siteOffset u ((normalIndex u.1).succAbove (u.2.1 j)) = sign (u.2.2 j) * q0 j := by
  have h := siteAxis_siteOffset_inner u j
  rw [siteAxis_inner_coordinate] at h
  cases hb : u.2.2 j <;> simp [sign, hb] at h ⊢ <;> linarith

theorem q0_pos {m : ℕ} (j : Fin m) : 0 < q0 j := by unfold q0; positivity

theorem abs_q0_lt_quarter {m : ℕ} (j : Fin m) : |q0 j| < 1 / 4 := by
  apply orbit_offset_below_quarter
  · positivity
  · positivity
  · exact_mod_cast Nat.succ_lt_succ j.isLt

/-- Every native offset has strict coordinate distance less than one quarter. -/
theorem siteOffset_coordinate_bound {m : ℕ} (u : Site m) (k : Fin (m + 1)) :
    |siteOffset u k| < 1 / 4 := by
  by_cases hk : k = normalIndex u.1
  · subst k
    simp
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hk
    let l : Fin m := u.2.1.symm j
    have hl : u.2.1 l = j := u.2.1.apply_symm_apply j
    rw [← hj, ← hl, siteOffset_tangent, abs_mul, abs_sign, one_mul]
    exact abs_q0_lt_quarter l

theorem abs_normalCoord {m : ℕ} (u : Site m) (x : Space m) :
    |normalCoord u x| =
      |x (normalIndex u.1) - siteCenter u (normalIndex u.1)| := by
  simp [normalCoord, outward_inner_coordinate, abs_mul]

theorem abs_tangentCoord {m : ℕ} (u : Site m) (x : Space m) (j : Fin m) :
    |tangentCoord u x j| =
      |x ((normalIndex u.1).succAbove (u.2.1 j)) -
        siteCenter u ((normalIndex u.1).succAbove (u.2.1 j))| := by
  simp [tangentCoord, siteAxis_inner_coordinate, abs_mul]

/-- A site shift changes no carrier-normal coordinate. -/
theorem normalCoord_eq_facet {m : ℕ} (u : Site m) (x : Space m) :
    normalCoord u x = ⟪outward u.1, x - facetCenter u.1⟫_ℝ := by
  simp [normalCoord, siteCenter, inner_sub_right, inner_add_right]

@[simp] theorem normalCoord_center {m : ℕ} (u : Site m) :
    normalCoord u (siteCenter u) = 0 := by simp [normalCoord]

@[simp] theorem tangentCoord_center {m : ℕ} (u : Site m) (j : Fin m) :
    tangentCoord u (siteCenter u) j = 0 := by simp [tangentCoord]

/-- The all-zero occupied cell supplies an explicit point in the carrier. -/
def zeroCell (m : ℕ) : Cell m :=
  ⟨fun _ => false, by intro h; have := congrFun h (0 : Fin (m + 1)); simp at this⟩

theorem zero_mem_carrier (m : ℕ) : (0 : Space m) ∈ carrier m := by
  apply Set.mem_iUnion.mpr
  refine ⟨zeroCell m, ?_⟩
  intro i
  norm_num [zeroCell, bit]

theorem carrier_nonempty (m : ℕ) : (carrier m).Nonempty := ⟨0, zero_mem_carrier m⟩

theorem unitCell_compact {m : ℕ} (a : Cell m) : IsCompact (unitCell a) := by
  have h := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).toHomeomorph.isCompact_preimage.mpr
    (isCompact_Icc (a := fun i => bit (a.val i)) (b := fun i => bit (a.val i) + 1))
  convert h using 1
  ext x
  simp only [unitCell, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Icc, Pi.le_def]
  exact forall_and

theorem carrier_compact (m : ℕ) : IsCompact (carrier m) :=
  isCompact_iUnion (fun a : Cell m => unitCell_compact a)

/-- A concrete bounding box for the finite carrier. -/
theorem carrier_coordinate_bounds {m : ℕ} {x : Space m} (hx : x ∈ carrier m)
    (i : Fin (m + 1)) : 0 ≤ x i ∧ x i ≤ 2 := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  have h := ha i
  cases hb : a.val i <;> simp [bit, hb] at h <;> constructor <;> linarith

/-- A quantifier-sized characterization of the union of all proper binary
 cells. No finite enumeration or geometric registration assumption is used. -/
theorem mem_carrier_iff {m : ℕ} (x : Space m) :
    x ∈ carrier m ↔ (∀ i, 0 ≤ x i ∧ x i ≤ 2) ∧ ∃ i, x i ≤ 1 := by
  classical
  constructor
  · intro hx
    refine ⟨fun i => carrier_coordinate_bounds hx i, ?_⟩
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    have hex : ∃ i, a.val i = false := by
      by_contra hn
      apply a.property
      funext i
      cases h : a.val i
      · exact False.elim (hn ⟨i, h⟩)
      · rfl
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simpa [bit, hi] using (ha i).2⟩
  · rintro ⟨hbox, j, hj⟩
    let a : Cell m := ⟨fun i => decide (1 < x i), by
      intro h
      have ht : decide (1 < x j) = true := congrFun h j
      have := of_decide_eq_true ht
      linarith⟩
    apply Set.mem_iUnion.mpr
    refine ⟨a, ?_⟩
    intro i
    by_cases hi : 1 < x i
    · simp only [a, bit, hi, decide_true, ↓reduceIte]
      exact ⟨hi.le, by linarith [(hbox i).2]⟩
    · simp only [a, bit, hi, decide_false, Bool.false_eq_true, ↓reduceIte, zero_add]
      exact ⟨(hbox i).1, le_of_not_gt hi⟩

/-- An open full-dimensional coordinate box about the exposed unit-facet
 center. Its tangent ranges are exactly the relative interior of that facet. -/
def facetNeighborhood {m : ℕ} (f : Facet m) : Set (Space m) :=
  {x | ∀ k, |x k - facetCenter f k| < 1 / 2}

theorem facetNeighborhood_isOpen {m : ℕ} (f : Facet m) :
    IsOpen (facetNeighborhood f) := by
  have h : facetNeighborhood f = ⋂ k, {x : Space m | |x k - facetCenter f k| < 1 / 2} := by
    ext x
    simp [facetNeighborhood]
  rw [h]
  apply isOpen_iInter_of_finite
  intro k
  exact isOpen_lt (((EuclideanSpace.proj k).continuous.sub continuous_const).abs) continuous_const

theorem mem_carrier_outer_iff {m : ℕ} (a : Cell m) (i : Fin (m + 1))
    (x : Space m) (hx : x ∈ facetNeighborhood (.inl (a, i))) :
    x ∈ carrier m ↔ if a.val i then x i ≤ 2 else 0 ≤ x i := by
  constructor
  · intro h
    have hbound := carrier_coordinate_bounds h i
    cases a.val i <;> simp <;> first | exact hbound.1 | exact hbound.2
  · intro h
    apply Set.mem_iUnion.mpr
    refine ⟨a, ?_⟩
    intro k
    have hrect := abs_lt.mp (hx k)
    by_cases hki : k = i
    · subst k
      cases hb : a.val i <;>
        simp [facetCenter, bit, hb] at hrect h ⊢ <;> constructor <;> linarith
    · cases hb : a.val k <;>
        simp [facetCenter, hki, bit, hb] at hrect ⊢ <;> constructor <;> linarith

theorem mem_carrier_inner_iff {m : ℕ} (i : Fin (m + 1)) (x : Space m)
    (hx : x ∈ facetNeighborhood (.inr i)) : x ∈ carrier m ↔ x i ≤ 1 := by
  have hnormal : 1 / 2 < x i ∧ x i < 3 / 2 := by
    have h := abs_lt.mp (hx i)
    simp [facetCenter] at h
    constructor <;> linarith
  have htangent : ∀ k, k ≠ i → 1 < x k ∧ x k < 2 := by
    intro k hki
    have h := abs_lt.mp (hx k)
    simp [facetCenter, hki] at h
    constructor <;> linarith
  rw [mem_carrier_iff]
  constructor
  · rintro ⟨_, k, hk⟩
    by_cases hki : k = i
    · simpa [hki] using hk
    · linarith [(htangent k hki).1]
  · intro h
    refine ⟨?_, i, h⟩
    intro k
    by_cases hki : k = i
    · subst k
      constructor <;> linarith [hnormal.1, hnormal.2]
    · exact ⟨by linarith [(htangent k hki).1], (htangent k hki).2.le⟩

/-- Every indexed native exposed facet has a proved local flat carrier chart.
 This concerns the actual finite union of unit cells, not an assumed carrier. -/
theorem mem_carrier_local_halfspace {m : ℕ} (f : Facet m) (x : Space m)
    (hx : x ∈ facetNeighborhood f) :
    x ∈ carrier m ↔ ⟪outward f, x - facetCenter f⟫_ℝ ≤ 0 := by
  rw [outward_inner_coordinate]
  cases f with
  | inl ai =>
    rcases ai with ⟨a, i⟩
    rw [mem_carrier_outer_iff a i x hx]
    cases hb : a.val i <;>
      simp [normalSign, normalIndex, facetCenter, sign, hb]
  | inr i =>
    rw [mem_carrier_inner_iff i x hx]
    simp [normalSign, normalIndex, facetCenter]

theorem eta_pos (m : ℕ) : 0 < eta m := by unfold eta; positivity

theorem rho_pos (m : ℕ) : 0 < rho m := by unfold rho; positivity

theorem eta_lt_rho (m : ℕ) : eta m < rho m := by
  unfold eta rho
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- The concrete native signed height inherits the previously checked
 global Lipschitz estimate, now with all axis and prime hypotheses discharged. -/
theorem siteHeight_lipschitz {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (x y : Space m) :
    |siteHeight a u x - siteHeight a u y| ≤
      ((J : ℝ) * pMax m J / denominator m J) * ‖x - y‖ := by
  have h := keyHeight_lipschitz (eta m) (a.value u : ℝ) (denominator m J : ℝ)
    (J : ℝ) (pMax m J : ℝ) (eta_pos m)
    (by exact_mod_cast (denominator_prime m J).pos) (a.bound u) (Nat.cast_nonneg _)
    (pMinus J) (pPlus J) (siteAxis u)
    (fun j => ⟨(pMinus_pos J j).le, pMinus_le_pMax J j⟩)
    (fun j => ⟨(pPlus_pos J j).le, pPlus_le_pMax J j⟩)
    (siteAxis_unit u) (x - siteCenter u) (y - siteCenter u)
  simpa only [siteHeight, sub_sub_sub_cancel_right] using h

theorem siteHeight_normal_shift {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (x : Space m) (s : ℝ) :
    siteHeight a u (x + s • outward u.1) = siteHeight a u x := by
  have h := keyHeight_normal_shift (eta m) (a.value u : ℝ) (denominator m J : ℝ)
    (pMinus J) (pPlus J) (siteAxis u) (outward u.1)
    (siteAxis_outward_inner u) (x - siteCenter u) s
  have hid : x + s • outward u.1 - siteCenter u = x - siteCenter u + s • outward u.1 := by abel
  simpa only [siteHeight, hid] using h

theorem siteCenter_mem_facetNeighborhood {m : ℕ} (u : Site m) :
    siteCenter u ∈ facetNeighborhood u.1 := by
  intro k
  have h := siteOffset_coordinate_bound u k
  simpa [siteCenter] using h.trans (by norm_num : (1 : ℝ) / 4 < 1 / 2)

/-- The actual native tent takes values between zero and one everywhere. -/
theorem native_profile_range {m : ℕ} [NeZero m] (J : ℕ) (u : Site m) (v : Space m) :
    0 ≤ keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) v ∧
    keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) v ≤ 1 := by
  let j : Fin m := 0
  have hmin := finiteLowerEnvelope_le
    (fun i v => min (1 + pMinus J i * ⟪siteAxis u i, v⟫_ℝ / eta m)
      (1 - pPlus J i * ⟪siteAxis u i, v⟫_ℝ / eta m)) v j
  have hb : min (1 + pMinus J j * ⟪siteAxis u j, v⟫_ℝ / eta m)
      (1 - pPlus J j * ⟪siteAxis u j, v⟫_ℝ / eta m) ≤ 1 := by
    by_cases hv : 0 ≤ ⟪siteAxis u j, v⟫_ℝ
    · have hp := div_nonneg (mul_nonneg (pPlus_pos J j).le hv) (eta_pos m).le
      exact (min_le_right _ _).trans (by linarith)
    · have hp := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (pMinus_pos J j).le (le_of_not_ge hv))
        (eta_pos m).le
      exact (min_le_left _ _).trans (by linarith)
  exact ⟨le_max_left _ _, max_le (by norm_num) (hmin.trans hb)⟩

/-- The signed graph never exceeds its advertised absolute height. -/
theorem siteHeight_abs_le {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (x : Space m) :
    |siteHeight a u x| ≤ eta m * (J : ℝ) / denominator m J := by
  have hN : 0 < (denominator m J : ℝ) := by exact_mod_cast (denominator_prime m J).pos
  have hprofile := native_profile_range J u (x - siteCenter u)
  unfold siteHeight keyHeight
  rw [abs_mul, abs_div, abs_mul, abs_of_pos (eta_pos m), abs_of_pos hN,
    abs_of_nonneg hprofile.1]
  calc
    eta m * |(a.value u : ℝ)| / denominator m J *
        keyTentProfile (eta m) (pMinus J) (pPlus J) (siteAxis u) (x - siteCenter u)
      ≤ eta m * |(a.value u : ℝ)| / denominator m J * 1 :=
        mul_le_mul_of_nonneg_left hprofile.2
          (div_nonneg (mul_nonneg (eta_pos m).le (abs_nonneg _)) hN.le)
    _ ≤ eta m * (J : ℝ) / denominator m J := by
      rw [mul_one]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (a.bound u) (eta_pos m).le) hN.le

theorem denominator_gt_coefficient_bound (m J : ℕ) : J < denominator m J := by
  have hp : 1 ≤ pMax m J := (keyPrime_prime J (2 * m - 1)).one_lt.le
  have hfactor : 1 ≤ 32 * (m + 1) := by omega
  have h := Nat.mul_le_mul_right J hfactor
  have h' := Nat.mul_le_mul_left (32 * (m + 1) * J) hp
  exact (by nlinarith : J ≤ 32 * (m + 1) * J * pMax m J).trans_lt (denominator_gt m J)

/-- Graph points are strictly inside the tube's normal strip, for every
 allowed coefficient input and either sign of the height. -/
theorem siteHeight_abs_lt_rho {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) (x : Space m) : |siteHeight a u x| < rho m := by
  have hN : 0 < (denominator m J : ℝ) := by exact_mod_cast (denominator_prime m J).pos
  have hJ : (J : ℝ) < denominator m J := by exact_mod_cast denominator_gt_coefficient_bound m J
  have hamp : eta m * (J : ℝ) / denominator m J < eta m := by
    apply (div_lt_iff₀ hN).mpr
    exact mul_lt_mul_of_pos_left hJ (eta_pos m)
  exact (siteHeight_abs_le a u x).trans_lt (hamp.trans (eta_lt_rho m))

#print axioms card_site
#print axioms carrier_compact
#print axioms siteHeight_lipschitz
#print axioms siteHeight_abs_lt_rho
#print axioms siteOffset_coordinate_bound
#print axioms mem_carrier_local_halfspace
#print axioms mem_carrier_iff
#print axioms zero_mem_carrier
#print axioms carrier_coordinate_bounds
#print axioms siteAxis_outward_inner
#print axioms nextPrime_min

end
end PhysicalRegistration.NativeChair
