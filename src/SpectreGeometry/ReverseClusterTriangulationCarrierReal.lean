module

public import SpectreGeometry.ReverseClusterTriangulationReal
public import SpectreGeometry.ReverseClusterTriangulationCoverAssembly

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate

theorem FamilyCover.sound {ps qs : List PolygonPacket}
    (hc : FamilyCover ps qs) (hp : familyCheckedB ps = true)
    (hq : familyCheckedB qs = true) : familyBody ps ⊆ familyBody qs := by
  intro x hx
  obtain ⟨p,hp',hxp⟩ := by simpa only [familyBody,mem_iUnion] using hx
  obtain ⟨t,ht⟩ := hc p hp'
  exact tree_covered_by_family qs hq _ t ht x (satisfies_unit_append _ _
    ((packetChecked_sound p (familyChecked_mem ps hp p hp') x).1 hxp))

theorem FamilyCover.antisymm {ps qs : List PolygonPacket}
    (hp : familyCheckedB ps = true) (hq : familyCheckedB qs = true)
    (hf : FamilyCover ps qs) (hb : FamilyCover qs ps) : familyBody ps = familyBody qs :=
  Subset.antisymm (hf.sound hp hq) (hb.sound hq hp)

def scaledGridKiteBody (n : Int) (c : Cell) : Set RealPoint :=
  integerHull ((cellVertices c).map (fun p => (n*p.1,n*p.2)))

def scaledClusterBody (n : Int) (kind : ClusterKind) : Set RealPoint :=
  ⋃ c ∈ clusterCells kind, scaledGridKiteBody n c

theorem familyBody_eq_scaledClusterBody (ps : List PolygonPacket)
    (n : Int) (kind : ClusterKind)
    (h : ps.map PolygonPacket.vertices =
      (clusterCells kind).map (fun c => (cellVertices c).map (fun p => (n*p.1,n*p.2)))) :
    familyBody ps = scaledClusterBody n kind := by
  ext x
  simp only [familyBody,scaledClusterBody,scaledGridKiteBody,mem_iUnion]
  constructor
  · rintro ⟨p,hp,hx⟩
    have hm : p.vertices ∈ (clusterCells kind).map
        (fun c => (cellVertices c).map (fun p => (n*p.1,n*p.2))) := by
      rw [←h]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
    exact ⟨c,hc,he.symm ▸ hx⟩
  · rintro ⟨c,hc,hx⟩
    have hm : (cellVertices c).map (fun p => (n*p.1,n*p.2)) ∈ ps.map PolygonPacket.vertices := by
      rw [h]
      exact List.mem_map.mpr ⟨c,hc,rfl⟩
    obtain ⟨p,hp,he⟩ := List.mem_map.mp hm
    exact ⟨p,hp,he.symm ▸ hx⟩

end
end SpectreGeometry.ReverseClusterTriangulation
