module

public import SpectreGeometry.ReversePlacedClusterCharts
public import SpectreGeometry.ReverseLocallyFiniteCarrier
public import SpectreGeometry.ReverseClusterBoundedDistance
public import SpectreGeometry.ReverseBoundedDistanceProper

@[expose] public section


/-! Closed whole-cluster chart assembly. Local chart existence and neighboring
forward agreement remain explicit inputs until their finite bindings are ready. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation

variable (hlocal : ∀ k : Fin 9,
  sourceHexCarrier (0,0) ≃ₜ rawClusterBody (clusterOfMark k))
variable (f : Position → State) (hf : GloballyLegal f)

def markedTargetCarrier (c : Position) : Set RealPoint :=
  placedClusterCarrier (f c).2 (markedAnchor f hf c) (clusterOfMark (f c).1)

def markedPlacedChart (c : Position) : sourceHexCarrier c ≃ₜ markedTargetCarrier f hf c :=
  placedClusterChart (hlocal (f c).1) (f c).2 c (markedAnchor f hf c)

def MarkedNeighborAgreement : Prop :=
  ∀ c d p (hp : p ∈ sourceHexCarrier c) (hq : p ∈ sourceHexCarrier (sourceHexNeighbor c d)),
    (markedPlacedChart hlocal f hf c ⟨p,hp⟩).val =
      (markedPlacedChart hlocal f hf (sourceHexNeighbor c d) ⟨p,hq⟩).val

/-- Every potential source overlap is a checked hex-neighbor overlap. -/
def markedCarrierAtlas (hagree : MarkedNeighborAgreement hlocal f hf) :
    LocallyFiniteCarrierAtlas RealPoint RealPoint Position where
  source := sourceHexCarrier
  target := markedTargetCarrier f hf
  chart := markedPlacedChart hlocal f hf
  source_closed := sourceHex_isClosed
  target_closed c := placedClusterCarrier_isClosed _ _ _
  source_locallyFinite := sourceHex_locallyFinite
  source_cover := sourceHex_plane_cover
  forward_agree c c' p hp hq := by
    by_cases he : c'=c
    · subst c'
      rfl
    · obtain ⟨d,rfl⟩ := sourceHex_intersection_neighbor he ⟨p,hp,hq⟩
      exact hagree c d p hp hq

theorem markedCarrierAtlas_carrier_inclusion (hagree : MarkedNeighborAgreement hlocal f hf)
    (c : Position) (p : RealPoint) (hp : p ∈ sourceHexCarrier c) :
    ∃ q ∈ rawClusterBody (clusterOfMark (f c).1),
      (markedCarrierAtlas hlocal f hf hagree).map p =
        markedAnchor f hf c+gridRotation (f c).2 q := by
  rw [(markedCarrierAtlas hlocal f hf hagree).map_on c p hp]
  have hm := (markedPlacedChart hlocal f hf c ⟨p,hp⟩).property
  obtain ⟨q,hq,he⟩ := hm
  exact ⟨q,hq,he.symm⟩

theorem markedCarrierAtlas_bounded_distance (hagree : MarkedNeighborAgreement hlocal f hf)
    (p : RealPoint) :
    dist ((markedCarrierAtlas hlocal f hf hagree).map p) (markedAnchorHomeomorph f hf p) ≤ 54 :=
  markedCluster_distance_to_anchor f hf _
    (markedCarrierAtlas_carrier_inclusion hlocal f hf hagree) p

theorem markedCarrierAtlas_isProperMap (hagree : MarkedNeighborAgreement hlocal f hf) :
    IsProperMap (markedCarrierAtlas hlocal f hf hagree).map :=
  isProperMap_of_bounded_distance_homeomorph (markedAnchorHomeomorph f hf)
    (markedCarrierAtlas hlocal f hf hagree).continuous_map (0:RealPoint) 54
    (markedCarrierAtlas_bounded_distance hlocal f hf hagree)

end
end SpectreGeometry.ReverseExistence
