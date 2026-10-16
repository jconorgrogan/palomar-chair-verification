/- SPDX-License-Identifier: Apache-2.0
Author and responsible maintainer: Conor Grogan. AI assistance: OpenAI assistant.
Independent higher-dimensional physical statement reference. Draft, unelaborated.
Only Mathlib is imported. No project theorem, body, registration premise, or proof
is used to specify these statements. This module proves no existence theorem.
-/
module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Isometry
set_option autoImplicit false
@[expose] public section
namespace HigherPhysicalReference
noncomputable section

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- All physical copies may use arbitrary isometries, including reflections. -/
def IsTiling {d : ℕ} (T : Set (Point d)) (tiles : Set (Set (Point d))) : Prop :=
  (∀ A ∈ tiles, ∃ g : Point d ≃ᵢ Point d, A = g '' T) ∧
  (∀ x, ∃ A ∈ tiles, x ∈ A) ∧
  (∀ A ∈ tiles, ∀ B ∈ tiles, A ≠ B → Disjoint (interior A) (interior B))

def translate {d : ℕ} (v : Point d) (A : Set (Point d)) : Set (Point d) :=
  (fun x => x + v) '' A

/-- A period preserves the physical tile collection. -/
def IsPeriod {d : ℕ} (tiles : Set (Set (Point d))) (v : Point d) : Prop :=
  ∀ A, A ∈ tiles ↔ translate v A ∈ tiles

def HasTiling {d : ℕ} (T : Set (Point d)) : Prop :=
  ∃ tiles, IsTiling T tiles

def IsAperiodic {d : ℕ} (T : Set (Point d)) : Prop :=
  ∀ tiles, IsTiling T tiles → ∀ v, IsPeriod tiles v → v = 0

def IsAperiodicMonotile {d : ℕ} (T : Set (Point d)) : Prop :=
  IsCompact T ∧ HasTiling T ∧ IsAperiodic T

/-- Exact quantified specification for the first higher-only endpoint. -/
def ExpectedGeFive : Prop :=
  ∀ (d : ℕ) (hd : 5 ≤ d),
    ∃ T : Set (EuclideanSpace ℝ (Fin d)),
      (interior T).Nonempty ∧ IsAperiodicMonotile T

/-- Exact quantified specification for the second higher-only endpoint. -/
def ExpectedGeThreeNeFour : Prop :=
  ∀ (d : ℕ) (hd : 3 ≤ d) (hne : d ≠ 4),
    ∃ T : Set (EuclideanSpace ℝ (Fin d)),
      (interior T).Nonempty ∧ IsAperiodicMonotile T
end
end HigherPhysicalReference
