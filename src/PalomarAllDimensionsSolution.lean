/- SPDX-License-Identifier: Apache-2.0
Author and responsible maintainer: Conor Grogan. AI assistance: OpenAI assistant.
Reconstructed source revision, 18 October 2026. Actual compilation, kernel
checking and the independent serialized physical-statement audit are pending.
-/
module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Isometry
public import NativeFinalAssembly.AllDimensions

@[expose] public section

set_option autoImplicit false

namespace PalomarAllDimensions

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def IsTiling {d : ℕ} (T : Set (Point d)) (tiles : Set (Set (Point d))) : Prop :=
  (∀ A ∈ tiles, ∃ g : Point d ≃ᵢ Point d, A = g '' T) ∧
  (∀ x, ∃ A ∈ tiles, x ∈ A) ∧
  (∀ A ∈ tiles, ∀ B ∈ tiles, A ≠ B → Disjoint (interior A) (interior B))

def translate {d : ℕ} (v : Point d) (A : Set (Point d)) : Set (Point d) :=
  (fun x => x + v) '' A

def IsPeriod {d : ℕ} (tiles : Set (Set (Point d))) (v : Point d) : Prop :=
  ∀ A, A ∈ tiles ↔ translate v A ∈ tiles

def HasTiling {d : ℕ} (T : Set (Point d)) : Prop :=
  ∃ tiles, IsTiling T tiles

def IsAperiodic {d : ℕ} (T : Set (Point d)) : Prop :=
  ∀ tiles, IsTiling T tiles → ∀ v, IsPeriod tiles v → v = 0

/-- Exact physical statement, proved by the closed native assembly. -/
theorem aperiodic_monotile_in_every_dimension
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ T : Set (Point d),
      IsCompact T ∧ (interior T).Nonempty ∧ HasTiling T ∧ IsAperiodic T := by
  exact NativeFinalAssembly.exists_physical_aperiodic_monotile_in_every_dimension_ge_two d hd

end PalomarAllDimensions
