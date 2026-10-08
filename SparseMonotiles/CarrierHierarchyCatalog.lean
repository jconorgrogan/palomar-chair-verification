module

public import SparseMonotiles.CarrierHierarchyPose

@[expose] public section

/-!
Local finite obligations, explicitly separated from the physical contact law.
`LocalCatalogFacts` will be checked on the supplied 284/408 tuples. Applying
these facts to arbitrary tilings still requires exact physical registration,
full-facet contact completeness, and the concrete contact-law bridge.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

instance {d : ℕ} (a : Bits d) : Decidable (Proper a) :=
  inferInstanceAs (Decidable (∃ i, a i = false))

instance {d : ℕ} (r : Equiv.Perm (Fin d)) (p q : Pose d) : Decidable (GaugeRel r p q) :=
  inferInstanceAs (Decidable (_ ∨ _))

def bitCode {d : ℕ} (a : Bits d) : ℕ := ∑ i, if a i then 2 ^ i.val else 0

/-- Canonical outer predecessor when the central tile is the root pose. -/
def incomingPose {d : ℕ} (a : Bits d) (σ : Equiv.Perm (Fin d)) : Pose d where
  perm := σ
  negative := a
  shift := fun i => 4 * bit a i - 1

def boxLower {d : ℕ} (p : Pose d) : Cell d :=
  fun i => p.shift i - if p.negative i then 2 else 0

def unitAxis {d : ℕ} (j : Fin d) : Cell d := fun i => if i = j then 1 else 0

/-- The four exact wall-box / omitted-cell families, independent of frame tags. -/
def WallGeometry {d : ℕ} (p : Pose d) : Prop := ∃ j : Fin d,
  (boxLower p = (fun i => 2 * unitAxis j i) ∧
    (hole p = (fun i => 1 + unitAxis j i) ∨ hole p = (fun i => 3 * unitAxis j i))) ∨
  (boxLower p = (fun i => -2 * unitAxis j i) ∧
    (hole p = (fun i => 1 - 3 * unitAxis j i) ∨ hole p = (fun i => -unitAxis j i)))

instance {d : ℕ} (p : Pose d) : Decidable (WallGeometry p) :=
  inferInstanceAs (Decidable (∃ _, _ ∨ _))

/-- These are finite pose properties, not assertions that a tiling has parents. -/
def LocalCatalogFacts {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (r : Equiv.Perm (Fin d)) (p : Pose d) : Prop :=
  (∃ b : Bool, ∀ i, p.shift i % 2 = if b then 1 else 0) ∧
  (IsChairCell (hole p) → Proper p.negative ∧
    GaugeRel r (incomingPose p.negative (σ p.negative)) p) ∧
  ((∀ i, p.shift i % 2 = 0) → WallGeometry p)

instance {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (r : Equiv.Perm (Fin d)) (p : Pose d) : Decidable (LocalCatalogFacts σ r p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Unsigned representative of the physical coordinate involution. -/
def unsignedPose {d : ℕ} (r : Equiv.Perm (Fin d)) : Pose d where
  perm := r
  negative := fun _ => false
  shift := fun _ => 0

/-- Finite covariance of the entire outer-child rule under the right gauge. -/
def EquivariantChildren {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (r : Equiv.Perm (Fin d)) : Prop := ∀ a : Bits d,
  compose (unsignedPose r) (compose (outerPose a (σ a)) (unsignedPose r)) =
    outerPose (fun i => a (r i)) (σ (fun i => a (r i)))

instance {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d)) (r : Equiv.Perm (Fin d)) :
    Decidable (EquivariantChildren σ r) := inferInstanceAs (Decidable (∀ a : Bits d, _))

def checkLocalCatalog {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (r : Equiv.Perm (Fin d)) (p : Pose d) : Bool := decide (LocalCatalogFacts σ r p)

theorem localCatalog_of_checked {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} {ps : List (Pose d)}
    (h : ps.all (checkLocalCatalog σ r) = true) :
    ∀ p ∈ ps, LocalCatalogFacts σ r p := by
  simpa only [List.all_eq_true, checkLocalCatalog, decide_eq_true_eq] using h
end SparseMonotiles.CarrierHierarchy
