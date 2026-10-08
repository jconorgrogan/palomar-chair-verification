module

public import SparseMonotiles.CarrierHierarchyPeriods
public import RegisteredTransportCore

@[expose] public section

/-!
# Checked adapter for the original compact project's full marked poses

STATUS: COMPILED, IMPORT/AXIOM-AUDITED AND LEANCHECKER-ACCEPTED, 2026-10-07.

This file imports the original `SparseMonotiles.CarrierHierarchyPeriods`.
All 34 original compact dependency modules were rebuilt using Lean 4.35.0-rc2
and the exact pinned official Mathlib revision. This concrete instantiation
passed compilation, import/axiom audit and the supported leanchecker.

No compact definitions are replaced or recreated here. Both cell types are
literally `Fin d → Int`. The conversion retains the entire signed permutation
and the exact integer shift; there is no frame quotient, coordinate change,
scale change, or replacement of full marked periods by anchor-only periods.

This adapter transports an explicitly supplied contact-language inclusion into
`ArithmeticAtlasContact`. It does not prove that inclusion, generated-E
legality, physical registration, or physical-period transport.
-/

namespace SparseMonotiles.CompactPoseAdapter
open Contact CarrierHierarchy

/-- Retain every output-row permutation, sign, and integer shift. -/
def toRP {d : Nat} (p : Contact.Pose d) : RegisteredPrime.Pose d where
  frame := {
    perm := p.perm
    inverse := p.perm.symm
    left_inverse := p.perm.symm_apply_apply
    right_inverse := p.perm.apply_symm_apply
    negative := p.negative
  }
  anchor := p.shift

/-- Recover the original equivalence-valued permutation and full marked pose. -/
def fromRP {d : Nat} (p : RegisteredPrime.Pose d) : Contact.Pose d where
  perm := {
    toFun := p.frame.perm
    invFun := p.frame.inverse
    left_inv := p.frame.left_inverse
    right_inv := p.frame.right_inverse
  }
  negative := p.frame.negative
  shift := p.anchor

private theorem compactPose_ext {d : Nat} {p q : Contact.Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative)
    (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  cases hp
  cases hn
  cases hs
  rfl

@[simp] theorem fromRP_toRP {d : Nat} (p : Contact.Pose d) :
    fromRP (toRP p) = p := by
  apply compactPose_ext
  · apply Equiv.ext
    intro i
    rfl
  · rfl
  · rfl

@[simp] theorem toRP_fromRP {d : Nat} (p : RegisteredPrime.Pose d) :
    toRP (fromRP p) = p := by
  apply RegisteredPrime.Pose.Same.eq
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- An equivalence of the exact pose types, not just of occupied carriers. -/
def poseEquiv (d : Nat) : Contact.Pose d ≃ RegisteredPrime.Pose d where
  toFun := toRP
  invFun := fromRP
  left_inv := fromRP_toRP
  right_inv := toRP_fromRP

theorem toRP_injective {d : Nat} : Function.Injective (@toRP d) := by
  intro p q h
  have he := congrArg fromRP h
  simpa only [fromRP_toRP] using he

theorem fromRP_injective {d : Nat} : Function.Injective (@fromRP d) := by
  intro p q h
  have he := congrArg toRP h
  simpa only [toRP_fromRP] using he

@[simp] theorem toRP_perm {d : Nat} (p : Contact.Pose d) (i : Fin d) :
    (toRP p).frame.perm i = p.perm i := rfl

@[simp] theorem toRP_inverse {d : Nat} (p : Contact.Pose d) (i : Fin d) :
    (toRP p).frame.inverse i = p.perm.symm i := rfl

@[simp] theorem toRP_negative {d : Nat} (p : Contact.Pose d) (i : Fin d) :
    (toRP p).frame.negative i = p.negative i := rfl

@[simp] theorem toRP_anchor {d : Nat} (p : Contact.Pose d) :
    (toRP p).anchor = p.shift := rfl

@[simp] theorem toRP_sign {d : Nat} (p : Contact.Pose d) (i : Fin d) :
    (toRP p).frame.sign i = p.sign i := rfl

/-- Includes the essential lower-corner correction in each negative row. -/
@[simp] theorem toRP_cell {d : Nat} (p : Contact.Pose d) (c : Contact.Cell d) :
    (toRP p).cell c = p.cell c := by
  funext i
  change p.shift i + p.sign i * c (p.perm i) -
      (if p.negative i then 1 else 0) =
    p.sign i * c (p.perm i) + p.shift i -
      (if p.negative i then 1 else 0)
  omega

@[simp] theorem fromRP_cell {d : Nat} (p : RegisteredPrime.Pose d)
    (c : RegisteredPrime.Cell d) : (fromRP p).cell c = p.cell c := by
  have h := toRP_cell (fromRP p) c
  simpa only [toRP_fromRP] using h.symm

@[simp] theorem toRP_compose {d : Nat} (p q : Contact.Pose d) :
    toRP (CarrierHierarchy.compose p q) = (toRP p).comp (toRP q) := by
  apply RegisteredPrime.Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  change p.sign i * q.shift (p.perm i) + p.shift i =
    p.shift i + p.sign i * q.shift (p.perm i)
  omega

@[simp] theorem toRP_inversePose {d : Nat} (p : Contact.Pose d) :
    toRP (CarrierHierarchy.inversePose p) = (toRP p).inv := by
  apply RegisteredPrime.Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  change -p.sign (p.perm.symm i) * p.shift (p.perm.symm i) =
    -(p.sign (p.perm.symm i) * p.shift (p.perm.symm i))
  ring

@[simp] theorem toRP_normalize {d : Nat} (p q : Contact.Pose d) :
    toRP (CarrierHierarchy.normalize p q) = (toRP p).relative (toRP q) := by
  unfold CarrierHierarchy.normalize RegisteredPrime.Pose.relative
  rw [toRP_compose, toRP_inversePose]

@[simp] theorem fromRP_comp {d : Nat} (p q : RegisteredPrime.Pose d) :
    fromRP (p.comp q) = CarrierHierarchy.compose (fromRP p) (fromRP q) := by
  apply toRP_injective
  simp only [toRP_fromRP, toRP_compose]

@[simp] theorem fromRP_inv {d : Nat} (p : RegisteredPrime.Pose d) :
    fromRP p.inv = CarrierHierarchy.inversePose (fromRP p) := by
  apply toRP_injective
  simp only [toRP_fromRP, toRP_inversePose]

@[simp] theorem fromRP_relative {d : Nat} (p q : RegisteredPrime.Pose d) :
    fromRP (p.relative q) = CarrierHierarchy.normalize (fromRP p) (fromRP q) := by
  apply toRP_injective
  simp only [toRP_fromRP, toRP_normalize]

/-- RP uses the inverse pose's cell action as its inverse-cell action. -/
@[simp] theorem toRP_inverseCell {d : Nat} (p : Contact.Pose d)
    (c : Contact.Cell d) : (toRP p).inv.cell c = p.inverseCell c := by
  apply RegisteredPrime.Pose.cell_injective (toRP p)
  rw [RegisteredPrime.Pose.cell_inv_cell, toRP_cell, Contact.Pose.cell_inverseCell]

@[simp] theorem fromRP_inverseCell {d : Nat} (p : RegisteredPrime.Pose d)
    (c : RegisteredPrime.Cell d) : (fromRP p).inverseCell c = p.inv.cell c := by
  have h := toRP_inverseCell (fromRP p) c
  simpa only [toRP_fromRP] using h.symm

/-- The two chair-cell predicates have identical definitions. -/
theorem chairCell_iff {d : Nat} (c : Contact.Cell d) :
    Contact.IsChairCell c ↔ RegisteredPrime.UnitChairCell c := Iff.rfl

/-- Exact occupancy, with no bounding-box approximation or frame quotient. -/
theorem occupies_iff {d : Nat} (p : Contact.Pose d) (c : Contact.Cell d) :
    CarrierHierarchy.Occupies p c ↔ RegisteredPrime.Occupies (toRP p) c := by
  rw [RegisteredPrime.occupies_inverse_iff, toRP_inverseCell]
  exact chairCell_iff _

theorem fromRP_occupies_iff {d : Nat} (p : RegisteredPrime.Pose d)
    (c : RegisteredPrime.Cell d) :
    CarrierHierarchy.Occupies (fromRP p) c ↔ RegisteredPrime.Occupies p c := by
  simpa only [toRP_fromRP] using occupies_iff (fromRP p) c

/-- The two discrete unit-face adjacency conventions are equivalent. -/
theorem adjacent_iff {d : Nat} (a b : Contact.Cell d) :
    CarrierHierarchy.AdjacentCells a b ↔ RegisteredPrime.Adjacent a b := by
  constructor
  · rintro ⟨j, hj, hrest⟩
    refine ⟨j, ?_, ?_⟩
    · omega
    · intro i hi
      exact (hrest i hi).symm
  · rintro ⟨j, hj, hrest⟩
    refine ⟨j, ?_, ?_⟩
    · omega
    · intro i hi
      exact (hrest i hi).symm

/-- Translate using the very same Int-valued vector in both presentations. -/
@[simp] theorem toRP_translate {d : Nat} (v : Contact.Cell d) (p : Contact.Pose d) :
    toRP (CarrierHierarchy.translatePose v p) =
      RegisteredPrime.AtlasPeriods.translate v (toRP p) := by
  apply RegisteredPrime.Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  change p.shift i + v i = v i + p.shift i
  omega

@[simp] theorem fromRP_translate {d : Nat} (v : RegisteredPrime.Cell d)
    (p : RegisteredPrime.Pose d) :
    fromRP (RegisteredPrime.AtlasPeriods.translate v p) =
      CarrierHierarchy.translatePose v (fromRP p) := by
  apply toRP_injective
  simp only [toRP_fromRP, toRP_translate]

/-- The generic transport is instantiated with the actual original predicates. -/
def compactBridge (d : Nat) : ExactRegisteredTransport.Bridge d (Contact.Pose d) where
  toRP := toRP
  fromRP := fromRP
  from_to := fromRP_toRP
  to_from := toRP_fromRP
  occupies := CarrierHierarchy.Occupies
  occupies_iff := occupies_iff
  adjacent := CarrierHierarchy.AdjacentCells
  adjacent_iff := adjacent_iff
  normalize := CarrierHierarchy.normalize
  normalize_toRP := toRP_normalize
  translate := CarrierHierarchy.translatePose
  translate_toRP := toRP_translate

/-- Unrestricted raw cell contact does not by itself supply disjointness. -/
theorem faceContact_iff {d : Nat} (p q : Contact.Pose d) :
    RegisteredPrime.FaceContact (toRP p) (toRP q) ↔
      (∀ c, ¬ (CarrierHierarchy.Occupies p c ∧ CarrierHierarchy.Occupies q c)) ∧
      CarrierHierarchy.CellContact p q :=
  (compactBridge d).faceContact_iff p q

/-- Actual coverage and nonoverlap are inherited from the original world. -/
def compactWorld {d : Nat} (W : CarrierHierarchy.RegisteredWorld d) :
    (compactBridge d).World where
  tiles := W.tiles
  covers := W.covers
  nonoverlap := fun p q hp hq c hpc hqc => W.disjoint p hp q hq c hpc hqc

/-- Exact image of an original full marked world in the RP presentation. -/
def toRegisteredWorld {d : Nat} (W : CarrierHierarchy.RegisteredWorld d) :
    RegisteredPrime.RegisteredWorld d := (compactWorld W).toRegistered

theorem toRegisteredWorld_mem {d : Nat} (W : CarrierHierarchy.RegisteredWorld d)
    (p : Contact.Pose d) : (toRegisteredWorld W).tiles (toRP p) ↔ p ∈ W.tiles :=
  (compactWorld W).toRegistered_mem p

/-- Inside a nonoverlapping world, the exact additional condition is distinctness. -/
theorem faceContact_iff_distinct {d : Nat} (W : CarrierHierarchy.RegisteredWorld d)
    (p q : Contact.Pose d) (hp : p ∈ W.tiles) (hq : q ∈ W.tiles) :
    RegisteredPrime.FaceContact (toRP p) (toRP q) ↔
      p ≠ q ∧ CarrierHierarchy.CellContact p q :=
  (compactWorld W).faceContact_iff_distinct p q hp hq

/-- Original legality has the same content, with only binder order changed. -/
theorem compactWorld_legal_iff {d : Nat} (W : CarrierHierarchy.RegisteredWorld d)
    (L : Set (Contact.Pose d)) : (compactWorld W).Legal L ↔ W.Legal L := by
  constructor
  · intro h p hp q hq hne hc
    exact h p q hp hq hne hc
  · intro h p q hp hq hne hc
    exact h p hp q hq hne hc

/-- Conditional atlas transport. The explicit inclusion premise is not discharged here. -/
theorem toRegisteredWorld_atlas_legal {d : Nat}
    (W : CarrierHierarchy.RegisteredWorld d) (L : Set (Contact.Pose d))
    (P : RegisteredPrime.Parameters) (hd : P.p = d)
    (atlas : ∀ p, p ∈ L → RegisteredPrime.ArithmeticAtlasContact P (hd ▸ toRP p))
    (legal : W.Legal L) :
    RegisteredPrime.ArithmeticAtlasLegal P (hd ▸ toRegisteredWorld W) := by
  exact (compactWorld W).toRegistered_atlas_legal P hd atlas
    ((compactWorld_legal_iff W L).mpr legal)

/-- The original marked period and RP marked period use the exact same vector. -/
theorem toRegisteredWorld_period_iff {d : Nat}
    (W : CarrierHierarchy.RegisteredWorld d) (v : Contact.Cell d) :
    RegisteredPrime.AtlasPeriods.TranslationPeriod (toRegisteredWorld W) v ↔
      W.IsPeriod v :=
  (compactWorld W).toRegistered_period_iff v

-- These axiom audits were executed in the successful concrete verification run.
#print axioms fromRP_toRP
#print axioms toRP_fromRP
#print axioms toRP_cell
#print axioms toRP_compose
#print axioms toRP_inversePose
#print axioms toRP_normalize
#print axioms toRP_inverseCell
#print axioms occupies_iff
#print axioms adjacent_iff
#print axioms toRP_translate
#print axioms faceContact_iff
#print axioms faceContact_iff_distinct
#print axioms toRegisteredWorld_atlas_legal
#print axioms toRegisteredWorld_period_iff

end SparseMonotiles.CompactPoseAdapter
