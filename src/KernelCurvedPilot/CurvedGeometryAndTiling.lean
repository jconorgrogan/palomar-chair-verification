/-
SPDX-License-Identifier: Apache-2.0
Author and responsible maintainer: Conor Grogan.
AI assistance: OpenAI dot reconstructed this ordinary source from the preserved
kernel-builder proof term. DRAFT: research dependencies have not been rebuilt.
The explicit result type is accepted only after independent raw contract audit;
no axiom, admitted proof, or historical generated object is an input here.
-/
module

public import SpectreGeometry.ReverseHomochiralExistence
public import LiteralPlanar.ForwardSeedTransfer

public section
open SpectreGeometry
open LiteralPlanar.Forward LiteralPlanar.FanBounds
namespace KernelCurvedPilot

theorem existing_curved_geometry_and_tiling :
    IsCompact curvedBody ∧ (interior curvedBody).Nonempty ∧
      closure (interior curvedBody) = curvedBody ∧
      frontier curvedBody = curvedBoundary ∧
      ∃ (I : Type) (p : I → EPlane ≃ᵢ EPlane),
        (∀ i, DirectPlacement (p i)) ∧
        (∀ x : EPlane, ∃ i, x ∈ p i '' curvedBody) ∧
        Pairwise (fun i j => Disjoint (interior (p i '' curvedBody))
          (interior (p j '' curvedBody))) ∧
        LocallyFinite (fun i => p i '' curvedBody) :=
  @LiteralPlanar.Forward.curved_geometry_and_tiling_of_original_seed
    SpectreGeometry.ReversePhysicalClusterCharts.exists_homochiral_P_tiling

end KernelCurvedPilot

