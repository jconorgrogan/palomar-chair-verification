/- SPDX-License-Identifier: Apache-2.0
Inactive configuration candidate. Lake elaboration and official preflight are pending.
Owned-library compilation selects one Lean worker and disables async elaboration.
-/
import Lake
open Lake DSL

package palomar_all_dimensions where
  defaultTargets := #["PalomarAllDimensions"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

lean_lib PalomarAllDimensions where
  moreLeanArgs := #["-j1", "-DElab.async=false"]
  srcDir := "src"
  roots := #[
    `AtlasPeriods,
    `AuditUniformPhysicalEndpoints,
    `ClarkSeed,
    `FinalAssemblyDraft,
    `KernelCurvedParentPilot,
    `KernelCurvedPilot,
    `KernelParentPilot,
    `KernelSeedPilot,
    `LiteralPlanar,
    `MeanObstruction,
    `NativeFinalAssembly,
    `NativeIndexedExistence,
    `PalomarAllDimensionsChallenge,
    `PalomarAllDimensionsSolution,
    `PhysicalRegistration,
    `PrimeFacetClosure,
    `ProductClosure,
    `RegisteredPrime,
    `SparseMonotiles,
    `SpectreClusters,
    `SpectreFinite,
    `SpectreGeometry,
    `Uniform,
    `UniformInspectorControl,
    `UniformPhysicalReference,
    `WeakRecognition,
    `WorldExistence,
    `closure_analysis]
  globs := #[
    .submodules `AtlasPeriods,
    .one `AuditUniformPhysicalEndpoints,
    .submodules `ClarkSeed,
    .submodules `FinalAssemblyDraft,
    .submodules `KernelCurvedParentPilot,
    .submodules `KernelCurvedPilot,
    .submodules `KernelParentPilot,
    .submodules `KernelSeedPilot,
    .submodules `LiteralPlanar,
    .submodules `MeanObstruction,
    .submodules `NativeFinalAssembly,
    .submodules `NativeIndexedExistence,
    .one `PalomarAllDimensionsChallenge,
    .one `PalomarAllDimensionsSolution,
    .submodules `PhysicalRegistration,
    .submodules `PrimeFacetClosure,
    .submodules `ProductClosure,
    .submodules `RegisteredPrime,
    .submodules `SparseMonotiles,
    .submodules `SpectreClusters,
    .submodules `SpectreFinite,
    .submodules `SpectreGeometry,
    .submodules `Uniform,
    .one `UniformInspectorControl,
    .one `UniformPhysicalReference,
    .submodules `WeakRecognition,
    .submodules `WorldExistence,
    .submodules `closure_analysis]
