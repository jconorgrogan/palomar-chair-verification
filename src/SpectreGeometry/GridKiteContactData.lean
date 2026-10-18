module

public import SpectreClusters.GridKiteProbeData
public import SpectreClusters.KiteContacts

@[expose] public section


/-! A finite strict separating-edge certificate for the 36 sector pairs and
25 bounded center offsets. The real offset bound is proved separately. -/
namespace SpectreGeometry.GridKiteContact
open SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate

def strictlySeparatedB (as bs : List Point) : Bool :=
  (polygonFacets as).any (fun line => bs.all (fun p => edgeValue line p ≤ -1))

def separatedB (as bs : List Point) : Bool :=
  strictlySeparatedB as bs || strictlySeparatedB bs as

end SpectreGeometry.GridKiteContact
