module

public import SpectreGeometry.ReverseMarkedAtlasBoundaryVertices
public import SpectreGeometry.ReverseMarkedBoundaryEdgeNeighborhood
public import SpectreGeometry.ReverseLocalStarBoundaryIndexBinding

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation ReverseLocalStarOccurrences ReverseFinitePL
open ReverseClusterNeighborCells ReverseClusterNeighborBinding

variable (hlocal : ∀ k : Fin 9, sourceHexCarrier (0,0) ≃ₜ rawClusterBody (clusterOfMark k))
variable (hboundary : ∀ k, MarkedBoundarySubintervalLaw k (fun x => (hlocal k x).val))
variable (f : Position → State) (hf : GloballyLegal f)

include hboundary in
/-- Every point of an open source side has an actual two-carrier target
neighborhood, including both kinds of subdivision vertices. -/
theorem marked_open_side_interior
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (hcert : ∀ i : Fin 217, SideGeometryCertificate i.val)
    (hbind : ∀ k d, SideGeometryBinding k d)
    (hchecked : ∀ i : Fin 35, configurationCheckedB (configuration i) = true)
    (hbinding : ∀ k r, MarkedConfigurationCertificate k r)
    (c : Position) (d : Fin 6) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1)
    (x : sourceHexCarrier c)
    (hx : x.val = AffineMap.lineMap (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1)) t) :
    (markedPlacedChart hlocal f hf c x).val ∈
      interior (markedTargetCarrier f hf c ∪
        markedTargetCarrier f hf (sourceHexNeighbor c d)) := by
  have hp := markedPlacedChart_pathParameter hlocal hboundary f hf c d t
    ⟨le_of_lt ht.1,le_of_lt ht.2⟩ x hx
  obtain ⟨j,hj,u,hu,hparam,hvalue⟩ := hp
  rw [realDevelopedPath_length] at hj hparam
  have hlen : (stateBoundaryIds (f c) d).length ≤ 12 :=
    all_boundary_indices_length_le_twelve (f c).1 (sideTurn (f c).2 d)
  by_cases hu0 : u=0
  · have hj0 : 0<j := by
      by_contra hn
      have hjz : j=0 := by omega
      rw [hu0,hjz] at hparam
      simp only [Nat.cast_zero,zero_add,zero_div] at hparam
      linarith [ht.1]
    apply marked_side_vertex_interior hlocal hboundary f hf hraw hrows hcert hbind
      c d ⟨j,by omega⟩ hj0 (by change j+1 < (stateBoundaryIds (f c) d).length; omega) x
    rw [hx,hparam,hu0,add_zero]
  by_cases hu1 : u=1
  · have hjend : j+2 < (stateBoundaryIds (f c) d).length := by
      by_contra hn
      have he : j+1 = (stateBoundaryIds (f c) d).length-1 := by omega
      have hd : (((stateBoundaryIds (f c) d).length-1:Nat):ℝ) ≠ 0 := by
        exact_mod_cast (show (stateBoundaryIds (f c) d).length-1 ≠ 0 by omega)
      have heR : (j:ℝ)+1 = ((stateBoundaryIds (f c) d).length-1:Nat) := by
        exact_mod_cast he
      rw [hu1,heR,div_self hd] at hparam
      linarith [ht.2]
    apply marked_side_vertex_interior hlocal hboundary f hf hraw hrows hcert hbind
      c d ⟨j+1,by omega⟩ (by change 0 < j+1; omega) hjend x
    rw [hx,hparam,hu1,Nat.cast_add,Nat.cast_one]
  have hu' : u ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),lt_of_le_of_ne hu.2 hu1⟩
  rw [hvalue]
  exact marked_boundary_open_edge_interior hchecked hbinding f hf c d j hj u hu'

/-- The two target carriers above are both incident at the source-side point. -/
theorem marked_open_side_targetStar_interior
    (hraw : ∀ big v, RawStarBinding big v) (hrows : IncidentRowsCorrect)
    (hcert : ∀ i : Fin 217, SideGeometryCertificate i.val)
    (hbind : ∀ k d, SideGeometryBinding k d)
    (hchecked : ∀ i : Fin 35, configurationCheckedB (configuration i) = true)
    (hbinding : ∀ k r, MarkedConfigurationCertificate k r)
    (c : Position) (d : Fin 6) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1)
    (x : sourceHexCarrier c)
    (hx : x.val = AffineMap.lineMap (sourceHexCornerAt c d) (sourceHexCornerAt c (d+1)) t) :
    (markedCarrierAtlas hlocal f hf (marked_neighbor_agreement hlocal hboundary f hf)).map x.val ∈
      interior ((markedCarrierAtlas hlocal f hf
        (marked_neighbor_agreement hlocal hboundary f hf)).targetStar x.val) := by
  let A := markedCarrierAtlas hlocal f hf (marked_neighbor_agreement hlocal hboundary f hf)
  have hneighbor : x.val ∈ sourceHexCarrier (sourceHexNeighbor c d) := by
    have hp : x.val ∈ sourceHexCarrier c ∩ sourceHexCarrier (sourceHexNeighbor c d) := by
      rw [sourceHex_neighbor_intersection_segment,hx]
      exact lineMap_mem_segment ℝ _ _ ⟨le_of_lt ht.1,le_of_lt ht.2⟩
    exact hp.2
  have hsub : markedTargetCarrier f hf c ∪ markedTargetCarrier f hf (sourceHexNeighbor c d) ⊆
      A.targetStar x.val := by
    rintro y (hy | hy)
    · exact mem_iUnion.mpr ⟨⟨c,x.property⟩,hy⟩
    · exact mem_iUnion.mpr ⟨⟨sourceHexNeighbor c d,hneighbor⟩,hy⟩
  have hi := marked_open_side_interior hlocal hboundary f hf hraw hrows hcert hbind
    hchecked hbinding c d t ht x hx
  change A.map x.val ∈ interior (A.targetStar x.val)
  rw [A.map_on c x.val x.property]
  exact interior_mono hsub hi

end
end SpectreGeometry.ReverseExistence
