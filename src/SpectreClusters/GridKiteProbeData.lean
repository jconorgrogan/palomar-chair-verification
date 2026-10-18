module

public import SpectreClusters.BodyBSPData

@[expose] public section


namespace SpectreClusters.GridKiteProbe
open BodyBSP

def localProbe (k : Turn) : Point := rotate k (1,0)
def probe (c : Cell) : Point := add (lattice c.center) (localProbe c.sector)
def localFacets (k : Turn) : List SpectreGeometry.HalfplaneCertificate.Constraint :=
  polygonFacets (localVertices k)
def containedB (s t : Turn) (delta : Point) : Bool :=
  (localFacets t).all fun line => 0 ≤ edgeValue line (sub (localProbe s) (lattice delta))

theorem localProbe_bounds : ∀ k : Turn,
    -1 ≤ (localProbe k).1 ∧ (localProbe k).1 ≤ 1 ∧
    -1 ≤ (localProbe k).2 ∧ (localProbe k).2 ≤ 1 := by decide

theorem localProbe_strict : ∀ k : Turn,
    (localFacets k).all (fun line => 0 < edgeValue line (localProbe k)) = true := by decide

theorem local_facets_convex : ∀ k : Turn,
    polygonPositiveB (localVertices k) = true := by decide

theorem local_facets_four : ∀ k : Turn, (localFacets k).length = 4 := by decide

theorem lattice_box_bound (delta : Point)
    (h : -3 ≤ (lattice delta).1 ∧ (lattice delta).1 ≤ 3 ∧
      -3 ≤ (lattice delta).2 ∧ (lattice delta).2 ≤ 3) :
    -1 ≤ delta.1 ∧ delta.1 ≤ 1 ∧ -1 ≤ delta.2 ∧ delta.2 ≤ 1 := by
  simp only [lattice] at h
  omega

set_option maxRecDepth 100000 in
 theorem finite_unique : ∀ s t : Turn, ∀ q r : Fin 3,
    containedB s t ((q.val : Int)-1,(r.val : Int)-1) = true ↔
      q.val = 1 ∧ r.val = 1 ∧ s = t := by decide

end SpectreClusters.GridKiteProbe
