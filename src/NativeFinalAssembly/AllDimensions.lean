/- SPDX-License-Identifier: Apache-2.0
Author and responsible maintainer: Conor Grogan. AI assistance: OpenAI assistant.
Reconstructed source revision, 18 October 2026. Actual compilation, kernel
checking and the independent serialized physical-statement audit are pending.
-/
module
public import NativeFinalAssembly.AllDimensionsOfParent
public import SpectreFinite.RadiusFivePruningHierarchy

@[expose] public section

set_option autoImplicit false

namespace NativeFinalAssembly

/-- The sole native premise is discharged by the exact checked C theorem. -/
theorem exists_physical_aperiodic_monotile_in_every_dimension_ge_two
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ T : Set (SparseMonotiles.Point d),
      IsCompact T ∧ (interior T).Nonempty ∧
      SparseMonotiles.HasTiling T ∧ SparseMonotiles.IsAperiodic T :=
  exists_physical_aperiodic_monotile_in_every_dimension_ge_two_of_parent
    SpectreFinite.HexSearch.RadiusFivePruning.certifiedParentOccurrenceTheorem d hd

end NativeFinalAssembly
