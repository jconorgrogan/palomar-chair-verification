/-
SPDX-License-Identifier: Apache-2.0
Author and responsible maintainer: Conor Grogan.
AI assistance: OpenAI dot reconstructed this ordinary source from the preserved
kernel-builder proof term. DRAFT: research dependencies have not been rebuilt.
The explicit result type is accepted only after independent raw contract audit;
no axiom, admitted proof, or historical generated object is an input here.
-/
module

public import SpectreGeometry.PolygonProductPlanarRigidityReduction
public import SpectreGeometry.PhysicalHierarchyFromParent

public section
open SpectreGeometry
namespace KernelParentPilot
universe u_1

theorem physical_polygon_product_period_eq_zero_of_parent :
    ∀ (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem)
      {ι : Type u_1} {f : ι → EFour ≃ᵢ EFour} (T : PolygonProductPhysicalTiling f)
      (v : EFour)
      (hperiod : Set.range (fun i => (fun z : EFour => z+v) '' (f i '' polygonProductKeyBody)) =
        Set.range (fun i => f i '' polygonProductKeyBody)), v = 0 :=
  fun (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem) =>
    @SpectreGeometry.physical_polygon_product_period_eq_zero_of_planar_rigidity.{u_1}
      (@SpectreGeometry.homochiral_physical_period_eq_zero_of_parent.{0} C)

end KernelParentPilot

