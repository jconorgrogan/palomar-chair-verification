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
public import LiteralPlanar.CurvedRigidityReduction
public import SpectreGeometry.PhysicalHierarchyFromParent

public section
open SpectreGeometry
open LiteralPlanar.Forward LiteralPlanar.FanBounds
namespace KernelCurvedParentPilot
universe u

theorem curved_period_eq_zero_of_parent :
    ∀ (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem)
      {J : Type u} (q : J → EPlane ≃ᵢ EPlane)
      (hcover : ∀ x, ∃ j, x ∈ q j '' LiteralPlanar.FanBounds.curvedBody)
      (hpack : Pairwise fun i j => Disjoint
        (interior (q i '' LiteralPlanar.FanBounds.curvedBody))
        (interior (q j '' LiteralPlanar.FanBounds.curvedBody)))
      (v : EPlane)
      (hperiod : Set.range (fun j => (fun x : EPlane => x+v) ''
        (q j '' LiteralPlanar.FanBounds.curvedBody)) =
        Set.range (fun j => q j '' LiteralPlanar.FanBounds.curvedBody)), v = 0 :=
  fun (C : SpectreFinite.HexSearch.NativeHierarchy.ParentOccurrenceTheorem) =>
    @LiteralPlanar.Forward.curved_period_eq_zero_of_seed_and_planar_rigidity.{u}
      SpectreGeometry.ReversePhysicalClusterCharts.exists_homochiral_P_tiling
      (@SpectreGeometry.homochiral_physical_period_eq_zero_of_parent.{u} C)

end KernelCurvedParentPilot

