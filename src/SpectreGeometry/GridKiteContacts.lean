module

public import SpectreGeometry.GridKiteContactSector0
public import SpectreGeometry.GridKiteContactSector1
public import SpectreGeometry.GridKiteContactSector2
public import SpectreGeometry.GridKiteContactSector3
public import SpectreGeometry.GridKiteContactSector4
public import SpectreGeometry.GridKiteContactSector5

@[expose] public section

namespace SpectreGeometry.GridKiteContact
open SpectreClusters SpectreClusters.BodyBSP
theorem finite_contact_or_separated : ∀ s t : Turn, ∀ q r : Fin 5,
    let a : Cell := ⟨(0,0),s⟩
    let b : Cell := ⟨((q.val : Int)-2,(r.val : Int)-2),t⟩
    cellContactB a b || separatedB (cellVertices a) (cellVertices b) = true := by
  exact (Fin.cases contact_or_separated_0 (Fin.cases contact_or_separated_1 (Fin.cases contact_or_separated_2 (Fin.cases contact_or_separated_3 (Fin.cases contact_or_separated_4 (Fin.cases contact_or_separated_5 (fun i => Fin.elim0 i)))))))
#print axioms finite_contact_or_separated
theorem finite_facets_nonnegative : ∀ s : Turn, ∀ q r : Fin 5,
    let a : Cell := ⟨((q.val : Int)-2,(r.val : Int)-2),s⟩
    ∀ line ∈ polygonFacets (cellVertices a), ∀ p ∈ cellVertices a,
      0 ≤ edgeValue line p := by
  exact (Fin.cases facets_nonnegative_0 (Fin.cases facets_nonnegative_1 (Fin.cases facets_nonnegative_2 (Fin.cases facets_nonnegative_3 (Fin.cases facets_nonnegative_4 (Fin.cases facets_nonnegative_5 (fun i => Fin.elim0 i)))))))
#print axioms finite_facets_nonnegative
end SpectreGeometry.GridKiteContact
