module

public import SpectreGeometry.ReverseClusterTriangulationCertificates

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
open HalfplaneCertificate SpectreClusters.BodyBSP

def FamilyCover (ps qs : List PolygonPacket) : Prop :=
  ∀ p ∈ ps, ∃ t, checkTree (p.facets ++ [unitFacet]) (familyFacets qs) t = true

theorem FamilyCover.append {ps qs target : List PolygonPacket}
    (hp : FamilyCover ps target) (hq : FamilyCover qs target) :
    FamilyCover (ps ++ qs) target := by
  intro p hpq
  rcases List.mem_append.mp hpq with h | h
  · exact hp p h
  · exact hq p h

end SpectreGeometry.ReverseClusterTriangulation
