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
public import SpectreGeometry.PolygonProductPhysicalExistence

public section
open SpectreGeometry
namespace KernelSeedPilot

theorem existing_physical_product_tiling :
    ∃ (I : Type) (f : I → EFour ≃ᵢ EFour), PolygonProductPhysicalTiling f :=
  @SpectreGeometry.exists_physical_product_tiling_of_planar_seed
    SpectreGeometry.ReversePhysicalClusterCharts.exists_homochiral_P_tiling

end KernelSeedPilot

