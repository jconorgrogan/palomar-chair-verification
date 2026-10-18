module

public import SpectreGeometry.GridKiteContactData

@[expose] public section

namespace SpectreGeometry.GridKiteContact
open SpectreClusters SpectreClusters.BodyBSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem contact_or_separated_4 : ∀ t : Turn, ∀ q r : Fin 5,
    let a : Cell := ⟨(0,0),4⟩
    let b : Cell := ⟨((q.val : Int)-2,(r.val : Int)-2),t⟩
    cellContactB a b || separatedB (cellVertices a) (cellVertices b) = true := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1600000 in
theorem facets_nonnegative_4 : ∀ q r : Fin 5,
    let a : Cell := ⟨((q.val : Int)-2,(r.val : Int)-2),4⟩
    ∀ line ∈ polygonFacets (cellVertices a), ∀ p ∈ cellVertices a,
      0 ≤ edgeValue line p := by decide
#print axioms contact_or_separated_4
#print axioms facets_nonnegative_4
end SpectreGeometry.GridKiteContact
