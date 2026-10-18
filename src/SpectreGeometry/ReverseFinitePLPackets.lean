module

public import SpectreGeometry.ReverseFinitePLInteger

@[expose] public section


/-! Direct binding of the packet checker's ordered vertex tables to the PL
mesh adapter. The real common-face soundness is used, not just its Boolean test. -/
namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP ReverseClusterTriangulation

theorem packet_binding_length (vs : List Point) (ts : List TriangleCode)
    (ps : List PolygonPacket)
    (hb : ps.map PolygonPacket.vertices = ts.map (triangleVertexList vs)) :
    ps.length = ts.length := by
  have h := congrArg List.length hb
  simpa only [List.length_map] using h

theorem packet_binding_at (vs : List Point) (ts : List TriangleCode)
    (ps : List PolygonPacket)
    (hb : ps.map PolygonPacket.vertices = ts.map (triangleVertexList vs))
    (i : Fin ts.length) :
    (ps.getD i.val default).vertices = triangleVertexList vs (ts.get i) := by
  have hi : i.val < ps.length := (packet_binding_length vs ts ps hb).symm ▸ i.isLt
  have h := congrArg (fun l : List (List Point) => l[i.val]?) hb
  simpa [List.getD_eq_getElem?_getD,hi,i.isLt] using h

theorem packet_binding_positive (vs : List Point) (ts : List TriangleCode)
    (ps : List PolygonPacket)
    (hb : ps.map PolygonPacket.vertices = ts.map (triangleVertexList vs))
    (hp : familyCheckedB ps = true) :
    ∀ t ∈ ts, polygonPositiveB (triangleVertexList vs t) = true := by
  intro t ht
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ht
  have hi : i.val < ps.length := (packet_binding_length vs ts ps hb).symm ▸ i.isLt
  have hc := familyChecked_mem ps hp (ps.getD i.val default) (getD_mem_of_lt ps i.val default hi)
  simp only [packetCheckedB,Bool.and_eq_true] at hc
  rw [←packet_binding_at vs ts ps hb i]
  exact hc.1.2

theorem packet_binding_faces (vs : List Point) (ts : List TriangleCode)
    (ps : List PolygonPacket)
    (hb : ps.map PolygonPacket.vertices = ts.map (triangleVertexList vs))
    (hf : FamilyHasFaces ps) (i j : Fin ts.length) :
    integerHull (triangleVertexList vs (ts.get i)) ∩
        integerHull (triangleVertexList vs (ts.get j)) =
      convexHull ℝ (integerVertexSet (triangleVertexList vs (ts.get i)) ∩
        integerVertexSet (triangleVertexList vs (ts.get j))) := by
  by_cases hij : i = j
  · subst j
    simp only [inter_self]
    rfl
  have hi : i.val < ps.length := (packet_binding_length vs ts ps hb).symm ▸ i.isLt
  have hj : j.val < ps.length := (packet_binding_length vs ts ps hb).symm ▸ j.isLt
  have hn : (⟨i.val,hi⟩ : Fin ps.length) ≠ ⟨j.val,hj⟩ := by
    intro h
    exact hij (Fin.ext (congrArg (fun z : Fin ps.length => z.val) h))
  have h := (hf ⟨i.val,hi⟩ ⟨j.val,hj⟩ hn).1
  simpa only [packet_binding_at vs ts ps hb i,packet_binding_at vs ts ps hb j] using h

/-- All inputs are the finite certificate packet's checked statements. -/
def IntegerMeshPair.ofPackets (source target : List Point) (ts : List TriangleCode)
    (ps qs : List PolygonPacket)
    (hlen : source.length = target.length)
    (hsn : source.Nodup) (htn : target.Nodup)
    (hib : ∀ t ∈ ts, ∀ n ∈ triangleIndices t, n < source.length)
    (hsb : ps.map PolygonPacket.vertices = ts.map (triangleVertexList source))
    (htb : qs.map PolygonPacket.vertices = ts.map (triangleVertexList target))
    (hsp : familyCheckedB ps = true) (htp : familyCheckedB qs = true)
    (hsf : FamilyHasFaces ps) (htf : FamilyHasFaces qs) : IntegerMeshPair where
  source := source
  target := target
  triangles := ts
  length_eq := hlen
  source_distinct := hsn
  target_distinct := htn
  index_bound := hib
  source_positive := packet_binding_positive source ts ps hsb hsp
  target_positive := packet_binding_positive target ts qs htb htp
  source_faces := packet_binding_faces source ts ps hsb hsf
  target_faces := packet_binding_faces target ts qs htb htf

theorem packet_binding_familyBody (vs : List Point) (ts : List TriangleCode)
    (ps : List PolygonPacket)
    (hb : ps.map PolygonPacket.vertices = ts.map (triangleVertexList vs)) :
    familyBody ps = ⋃ i : Fin ts.length, integerHull (triangleVertexList vs (ts.get i)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨p,hp,hxp⟩ := by simpa only [familyBody,mem_iUnion] using hx
    have hm : p.vertices ∈ ts.map (triangleVertexList vs) := by
      rw [←hb]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    obtain ⟨t,ht,he⟩ := List.mem_map.mp hm
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ht
    exact mem_iUnion.mpr ⟨i,by rwa [he]⟩
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    have hib : i.val < ps.length := (packet_binding_length vs ts ps hb).symm ▸ i.isLt
    apply mem_iUnion.mpr ⟨ps.getD i.val default,?_⟩
    apply mem_iUnion.mpr ⟨getD_mem_of_lt ps i.val default hib,?_⟩
    rwa [packet_binding_at vs ts ps hb i]

end
end SpectreGeometry.ReverseFinitePL
