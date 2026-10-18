module

public import SpectreGeometry.DirectIsometryFrames
public import SpectreGeometry.UnitEdgeAlignment
public import SpectreGeometry.NonvertexConnectivity

@[expose] public section


/-! Derivation of twelve relative rotations in every genuine homochiral
physical tiling. No finite-pose, edge-to-edge, or relative-angle premise is
used. Translational whole-unit-edge registration remains separate. -/
namespace SpectreGeometry
noncomputable section

theorem complexMulReal_direction_zero (x : RealPoint) : complexMulReal x (realDirection 0) = x := by
  simp [complexMulReal,realDirection,realize,direction,directions,Quad3.eval]

theorem realDirection_opposite (i : Fin 12) :
    realDirection (directionAdd i 6) = -realDirection i := by
  rw [←realDirection_multiply]
  have h6 : realDirection 6 = (-1,0) := by
    norm_num [realDirection,realize,direction,directions,Quad3.eval]
  rw [h6]
  apply Prod.ext <;> simp [complexMulReal]

/-- Equality of actual linear frames modulo one of the twelve proved rotations. -/
def CyclicFrameRelated (f g : EPlane ≃ᵢ EPlane) : Prop :=
  ∃ k : Fin 12, ∀ x : RealPoint, coordinateAction g x = coordinateAction f (rotate k x)

theorem cyclicFrameRelated_refl (f : EPlane ≃ᵢ EPlane) : CyclicFrameRelated f f :=
  ⟨0,by intro x; rw [rotate_zero]⟩

theorem cyclicFrameRelated_trans {f g h : EPlane ≃ᵢ EPlane}
    (hfg : CyclicFrameRelated f g) (hgh : CyclicFrameRelated g h) : CyclicFrameRelated f h := by
  obtain ⟨a,ha⟩ := hfg
  obtain ⟨b,hb⟩ := hgh
  exact ⟨directionAdd a b,fun x => by rw [hb,ha,rotate_add]⟩

theorem direct_equal_directions_cyclic (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) (i j : Fin 12)
    (hdir : coordinateAction f (realDirection i) = coordinateAction g (realDirection j)) :
    CyclicFrameRelated f g := by
  rw [direct_coordinateAction f hf,direct_coordinateAction g hg] at hdir
  have hh := congrArg (fun z => complexMulReal z (realDirection (directionInverse j))) hdir
  rw [←complexMulReal_assoc,←complexMulReal_assoc,realDirection_multiply,
    realDirection_multiply,direction_inverse_right,complexMulReal_direction_zero] at hh
  refine ⟨directionAdd i (directionInverse j),?_⟩
  intro x
  rw [direct_coordinateAction g hg,direct_coordinateAction f hf,←hh,←complexMulReal_assoc]
  rfl

theorem direct_aligned_directions_cyclic (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) (i j : Fin 12)
    (hdir : coordinateAction f (realDirection i) = coordinateAction g (realDirection j) ∨
      coordinateAction f (realDirection i) = -coordinateAction g (realDirection j)) :
    CyclicFrameRelated f g := by
  rcases hdir with h | h
  · exact direct_equal_directions_cyclic f g hf hg i j h
  · apply direct_equal_directions_cyclic f g hf hg i (directionAdd j 6)
    rw [realDirection_opposite,map_neg]
    exact h

theorem direct_aligned_edges_cyclic (f g : EPlane ≃ᵢ EPlane)
    (hf : DirectPlacement f) (hg : DirectPlacement g) (i j : Fin 14)
    (hdir : placedEdgeVector f i = placedEdgeVector g j ∨
      placedEdgeVector f i = -placedEdgeVector g j) : CyclicFrameRelated f g := by
  apply direct_aligned_directions_cyclic f g hf hg (edgeTurn i) (edgeTurn j)
  rw [←real_edge_direction,←real_edge_direction,coordinateAction_edge,coordinateAction_edge]
  rcases hdir with h | h
  · exact Or.inl (congrArg euclideanCoordinates.symm h)
  · apply Or.inr
    have hh := congrArg coordinateLinearEquiv.symm h
    rw [map_neg] at hh
    exact hh

/-- Every actual nonvertex contact propagates the twelve-frame relation. -/
theorem direct_nonvertex_contact_cyclic {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    {i j : ι} (hcontact : CompactTilingIncidence.ContactAway
      (fun k => f k '' euclideanBody) (CompactTilingIncidence.placedVertices f) i j) :
    CyclicFrameRelated (f i) (f j) := by
  by_cases hij : i = j
  · subst j; exact cyclicFrameRelated_refl (f i)
  obtain ⟨x,hi,hj,hnot⟩ := hcontact
  have hvertex : ∀ k : ι, ∀ e : Fin 14, x ≠ f k (euclideanVertex e) := by
    intro k e he
    exact hnot ⟨(k,e),he.symm⟩
  obtain ⟨a,b,hab⟩ := packing_nonvertex_contact_unit_vectors f hdisjoint hij hi hj hvertex
  exact direct_aligned_edges_cyclic (f i) (f j) (hdirect i) (hdirect j) a b hab

/-- Twelve relative rotations are a theorem of every genuine direct-isometry
physical tiling of the exact carrier, rather than an admissible-pose restriction. -/
theorem homochiral_tiling_cyclic_frames {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (i j : ι) :
    ∃ k : Fin 12, ∀ x : RealPoint, coordinateAction (f j) x = coordinateAction (f i) (rotate k x) := by
  have hp := CompactTilingIncidence.polygon_tiling_nonvertex_contact_connected f hdisjoint hcover i j
  change CyclicFrameRelated (f i) (f j)
  induction hp with
  | refl => exact cyclicFrameRelated_refl _
  | @tail a b hab hc ih =>
      exact cyclicFrameRelated_trans ih (direct_nonvertex_contact_cyclic f hdirect hdisjoint hc)

end
end SpectreGeometry
