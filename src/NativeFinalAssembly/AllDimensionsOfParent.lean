/- SPDX-License-Identifier: Apache-2.0
Author and responsible maintainer: Conor Grogan. AI assistance: OpenAI assistant.
Reconstructed source revision, 18 October 2026. Actual compilation, kernel
checking and the independent serialized physical-statement audit are pending.
-/
module
public import NativeFinalAssembly.CurvedOfParent
public import NativeFinalAssembly.KeyedProductOfParent
public import ClarkSeed.PhysicalDimensions

@[expose] public section

set_option autoImplicit false

namespace NativeFinalAssembly

/-- One physical shape for each dimension, with the native premise explicit. -/
theorem exists_model_monotile_in_every_dimension_ge_two_of_parent
    (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem)
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ T : Set (SparseMonotiles.Point d),
      (interior T).Nonempty ∧ SparseMonotiles.IsAperiodicMonotile T := by
  by_cases h2 : d = 2
  · subst d
    exact ⟨LiteralPlanar.FanBounds.curvedBody, curved_monotile_of_parent C⟩
  by_cases h4 : d = 4
  · subst d
    exact ⟨SpectreGeometry.polygonProductKeyBody, keyed_product_monotile_of_parent C⟩
  exact ClarkSeed.exists_physical_aperiodic_monotile_of_ge_three_ne_four d (by omega) h4

/-- Expanded physical statement with no concealed hierarchy premise. -/
theorem exists_physical_aperiodic_monotile_in_every_dimension_ge_two_of_parent
    (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem)
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ T : Set (SparseMonotiles.Point d),
      IsCompact T ∧ (interior T).Nonempty ∧
      SparseMonotiles.HasTiling T ∧ SparseMonotiles.IsAperiodic T := by
  obtain ⟨T, hi, hc, ht, ha⟩ :=
    exists_model_monotile_in_every_dimension_ge_two_of_parent C d hd
  exact ⟨T, hc, hi, ht, ha⟩

end NativeFinalAssembly
