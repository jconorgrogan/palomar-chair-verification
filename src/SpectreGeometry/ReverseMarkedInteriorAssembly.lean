module

public import SpectreGeometry.ReverseMarkedClusterInteriorCases
public import SpectreGeometry.ReverseLocalStarInteriorSoundness
public import SpectreGeometry.ReverseMarkedMeshInternalEdges
public import SpectreGeometry.ReverseMeshEdgeIncidenceSoundness
public import SpectreGeometry.ReverseMeshBoundaryEdgeSoundness

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL.MarkedMeshCertificate
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation ReverseExistence
open ReverseLocalStarOccurrences ReverseMeshEdgeIncidence
variable {k : Fin 9} (C : MarkedMeshCertificate k)

private theorem nondegenerate_vertex_injective (v : Fin 3 → Plane)
    (h : triangleDet v ≠ 0) : Function.Injective v := by
  intro a b he
  have hs : standardVertex a = standardVertex b := (triangleFrame v h).injective (by
    simpa only [triangleFrame_vertex] using he)
  fin_cases a <;> fin_cases b <;> simp_all [standardVertex,Fin.reduceFinMk]

private theorem edge_incidence_pair
    (hcert : ∀ big i, EdgeIncidenceCertificate big i)
    (i : Fin (meshTriangles k).length) (v w : Fin 3) (hvw : v ≠ w) :
    (∃ j : Fin (meshTriangles k).length, j ≠ i ∧
      codeIndex ((meshTriangles k).get i) v ∈ triangleIndices ((meshTriangles k).get j) ∧
      codeIndex ((meshTriangles k).get i) w ∈ triangleIndices ((meshTriangles k).get j)) ∨
    (codeIndex ((meshTriangles k).get i) v < boundarySize (k.val != 0) ∧
      codeIndex ((meshTriangles k).get i) w < boundarySize (k.val != 0) ∧
      ((codeIndex ((meshTriangles k).get i) v+1)%boundarySize (k.val != 0) =
        codeIndex ((meshTriangles k).get i) w ∨
       (codeIndex ((meshTriangles k).get i) w+1)%boundarySize (k.val != 0) =
        codeIndex ((meshTriangles k).get i) v)) := by
  obtain ⟨e,he⟩ := distinct_vertices_cyclic_edge v w hvw
  rcases he with ⟨hv,hw⟩ | ⟨hw,hv⟩
  · rw [hv,hw]
    exact actual_edge_incidence hcert k i e
  · rw [hv,hw]
    rcases actual_edge_incidence hcert k i e with ⟨j,hji,hv,hw⟩ | ⟨hv,hw,hadj⟩
    · exact Or.inl ⟨j,hji,hw,hv⟩
    · exact Or.inr ⟨hw,hv,hadj.symm⟩

/-- A complete finite interior-star certificate puts each nonboundary target
vertex in the ambient interior of its actual raw marked cluster. -/
theorem raw_interior_vertex
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (hcert : ∀ big v, InteriorFastCertificate big v)
    (v : Nat) (hv : v < (targetVertices k).length) (hnb : ¬IsBoundaryIndex k v) :
    (1/6:ℝ) • integerPoint (targetVertex k v) ∈
      interior (rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k)) := by
  let H := axialMotionHomeomorph 0 0
  have hi := placed_interior_vertex hraw hrows hcert k 0 v 0 hv hnb
  change H ((1/6:ℝ) • integerPoint (targetVertex k v)) ∈
    interior (H '' rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k)) at hi
  rw [←H.image_interior] at hi
  obtain ⟨y,hy,he⟩ := hi
  have he' := H.injective he
  rwa [he'] at hy

/-- The concrete marked mesh carries every source-hex interior point into the
ambient interior of the raw target cluster. The four finite certificate
families are explicit assumptions until their individual checked aggregates
are assembled. -/
theorem markedClusterHomeomorph_interior
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (hstar : ∀ big v, InteriorFastCertificate big v)
    (hedges : ∀ big i, EdgeIncidenceCertificate big i)
    (hboundary : ∀ k i, BoundaryEdgeCertificate k i)
    (x : sourceHexCarrier (0,0)) (hx : x.val ∈ interior (sourceHexCarrier (0,0))) :
    (C.markedClusterHomeomorph x).val ∈
      interior (rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k)) := by
  apply C.markedClusterHomeomorph_mem_interior_of_boundary x _ Subset.rfl
  · intro i v he
    have hv := all_mesh_indices_bound k _ (List.get_mem _ i) _ (codeIndex_mem _ v)
    apply raw_interior_vertex hraw hrows hstar _ hv.2
    intro hb
    exact boundary_index_not_interior k _ hb (he ▸ hx)
  · intro i v w hvw t ht he
    rcases edge_incidence_pair hedges i v w hvw with ⟨j,hji,hnj,hmj⟩ | ⟨hn,hm,hadj⟩
    · let n := C.markedIntegerMesh.meshIndex i v
      let m := C.markedIntegerMesh.meshIndex i w
      have hnm : n ≠ m := by
        intro heq
        apply hvw
        apply nondegenerate_vertex_injective
          (C.markedIntegerMesh.meshPair.sourceVertex ∘ C.markedIntegerMesh.meshPair.index i)
          (C.markedIntegerMesh.meshPair.source_nondegenerate i)
        exact congrArg C.markedIntegerMesh.sourceVertex heq
      exact C.internal_edge_interior i j (Ne.symm hji) n m hnm
        (codeIndex_mem _ v) (codeIndex_mem _ w) hnj hmj t ht
    · exact False.elim (mesh_boundary_edge_not_interior hboundary k _ _ hn hm hadj t (he ▸ hx))

end
end SpectreGeometry.ReverseFinitePL.MarkedMeshCertificate
