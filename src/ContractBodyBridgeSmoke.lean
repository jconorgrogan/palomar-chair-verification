/- SPDX-License-Identifier: Apache-2.0
Real source diagnostic only. Does not prove either Challenge theorem.
Requires genuine modern-module migration of BODY_BRIDGE_CLOSURE.json sources. -/
module
public import PalomarCurvedChallenge
public import PalomarKeyedProductChallenge
public import LiteralPlanar.FanTileMapImage
public import SpectreGeometry.PolygonProductKeyBody
public section

namespace PalomarCurved
theorem body_bridge_smoke : curvedBody = LiteralPlanar.FanBounds.curvedBody := rfl
#print axioms body_bridge_smoke
end PalomarCurved

namespace PalomarKeyedProduct
private theorem rawProduct_eq : rawProduct = SpectreGeometry.polygonProductBody := rfl
private theorem keyMap_eq (s : KeySite) :
    keyMap s = (SpectreGeometry.productKeyAffineIsometry s : Four → Four) := by
  funext w
  exact (SpectreGeometry.productKeyAffineIsometry_apply s w).symm
private theorem collar_eq (s : KeySite) : collar s = SpectreGeometry.productKeyCollar s := by
  unfold collar SpectreGeometry.productKeyCollar
  rw [keyMap_eq]
  rfl
private theorem hypograph_eq (s : KeySite) :
    hypograph s = SpectreGeometry.productKeyHypograph s := rfl
theorem body_bridge_smoke :
    keyedProduct = SpectreGeometry.polygonProductKeyBody := by
  simp only [keyedProduct, SpectreGeometry.polygonProductKeyBody,
    PhysicalRegistration.replaceTubes, rawProduct_eq, collar_eq, hypograph_eq]

#print axioms body_bridge_smoke
end PalomarKeyedProduct
