module

public import SpectreFinite.ParentBoundaryFrames

@[expose] public section


/-! Transfers of the frame witnesses, with a visible global-shape hypothesis
where a radius-five projection is identified with an actual complete parent. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary

theorem childAgreement_congr (f g : Position → State)
    (he : ∀ x ∈ hexRegion 5, f x = g x) (a : Position) (t : Fin 6) (j : TileKind) :
    ChildAgreement f a t j ↔ ChildAgreement g a t j := by
  constructor <;> intro h c hc hx
  · rw [← he _ ((inFive_iff _).mp hx)]
    exact h c hc hx
  · rw [he _ ((inFive_iff _).mp hx)]
    exact h c hc hx

theorem matchingKinds_congr (f g : Position → State)
    (he : ∀ x ∈ hexRegion 5, f x = g x) (a : Position) (t : Fin 6) :
    matchingKinds f a t = matchingKinds g a t := by
  unfold matchingKinds
  apply List.filter_congr
  intro j _
  simp only [childAgreement_congr f g he a t j]

theorem frameRows_local (f g : Position → State)
    (he : ∀ x ∈ hexRegion 5, f x = g x) (k : TileKind) (ns : List Position)
    (frames : List FrameInfo) (hg : FrameGeometry k ns frames) (h : FrameRows f frames) :
    FrameRows g frames := by
  intro s
  rw [← he _ ((inFive_iff _).mp (hg.2.2.1 s)), ← matchingKinds_congr f g he]
  exact h s

theorem framedRootStructure_encodedPatch (row : List State)
    (h : FramedRootStructure (indexedField row)) :
    FramedRootStructure (patchState (encodedPatch row)) := by
  obtain ⟨k,ns,frames,hp,hb,hg,hf⟩ := h
  refine ⟨k,ns,frames,?_,?_,hg,?_⟩
  · rw [encodedPatch_rootParent]
    exact hp
  · exact structure_local _ _ k ns (fun x hx =>
      (encodedPatch_owners row x (support_radiusThree k x hx)).symm) hb
  · apply frameRows_local _ _ _ k ns frames hg hf
    intro x hx
    exact (patchState_restriction _ _ _ hx).symm

theorem framedRootStructure_extract (f : Position → State) (center : Position)
    (h : FramedRootStructure (patchState (extract f center (hexRegion 5)))) :
    FramedRootStructure (shiftedField f center) := by
  obtain ⟨k,ns,frames,hp,hb,hg,hf⟩ := h
  refine ⟨k,ns,frames,?_,?_,hg,?_⟩
  · rw [rootParent_extract] at hp
    exact hp
  · exact structure_local _ _ k ns (fun x hx =>
      owners_extract f center (hexRegion 5) x
        (radiusThree_candidates_covered x (support_radiusThree k x hx))) hb
  · apply frameRows_local _ _ _ k ns frames hg hf
    intro x hx
    exact patchState_restriction _ _ _ hx

theorem frames_of_radiusFive_certificate (family : List Patch)
    (hc : ∀ p ∈ family, patchState p (0,0) = (0,0) → FramedRootStructure (patchState p))
    (f : Position → State) (hocc : OccurrenceComplete f (hexRegion 5) family)
    (center : Position) (hg : f center = (0,0)) : FramedRootStructure (shiftedField f center) := by
  apply framedRootStructure_extract
  apply hc _ (hocc center)
  change patchState (restriction (shiftedField f center) (hexRegion 5)) (0,0) = (0,0)
  rw [patchState_restriction _ _ _ (by decide)]
  simpa [shiftedField,addPos] using hg

private theorem rootParent_value (f : Position → State) (x : Position) (s : State)
    (h : (x,s) ∈ rootParent f) : s = f x := by
  obtain ⟨y,_,hy⟩ := List.mem_map.mp h
  have hx : y = x := congrArg Prod.fst hy
  rw [hx] at hy
  exact (congrArg Prod.snd hy).symm

/-- An actual complete parent shape necessarily passes the weaker displayed
child-state test. This is the bridge that prevents treating projections as
complete parents by definition. -/
theorem actual_parent_agrees (f : Position → State) (a : Position)
    (t : Fin 6) (j : TileKind)
    (hp : rootParent (rotatedField (inverseTurn t) (shiftedField f a)) = childPatch j) :
    ChildAgreement f a t j := by
  intro c hc _
  have hm : (pos c,(c.kind,c.turn)) ∈
      rootParent (rotatedField (inverseTurn t) (shiftedField f a)) := by
    rw [hp]
    exact List.mem_map.mpr ⟨c,hc,rfl⟩
  have hs := rootParent_value _ _ _ hm
  unfold placedPosition
  rw [normalized_field_value f a t (pos c), ← hs]

/-- The selected candidate kind equals the actual complete neighboring shape,
provided that complete shape has independently been established. -/
theorem actual_neighbor_kind (f : Position → State) (frames : List FrameInfo)
    (hf : FrameRows f frames) (s : Fin 6) (j : TileKind)
    (hp : rootParent (rotatedField (inverseTurn (frameAt frames s).turn)
      (shiftedField f (frameAt frames s).anchor)) = childPatch j) :
    j = (frameAt frames s).kind := by
  have hm := (mem_matchingKinds_iff f (frameAt frames s).anchor (frameAt frames s).turn j).mpr
    (actual_parent_agrees f _ _ j hp)
  rw [(hf s).2] at hm
  simpa using hm

/-- The finite mating/triangle witnesses bind to the actual neighboring parents
under the explicit global nine-parent-shape theorem. No such theorem is assumed
as an axiom, nor is any coarse-grid flatness conclusion asserted here. -/
theorem neighbor_patterns_of_global_shape (f : Position → State)
    (frames : List FrameInfo) (hf : FrameRows f frames)
    (hshape : ∀ a : Position, ∀ t : Fin 6, f a = (0,t) →
      ListedRootParent (rotatedField (inverseTurn t) (shiftedField f a))) :
    ∀ s : Fin 6,
      rootParent (rotatedField (inverseTurn (frameAt frames s).turn)
        (shiftedField f (frameAt frames s).anchor)) = childPatch (frameAt frames s).kind := by
  intro s
  obtain ⟨j,hj,_⟩ := listedRootParent_selected _ (hshape _ _ (hf s).1)
  rw [actual_neighbor_kind f frames hf s j hj] at hj
  exact hj

#print axioms framedRootStructure_encodedPatch
#print axioms frames_of_radiusFive_certificate
#print axioms actual_parent_agrees
#print axioms actual_neighbor_kind
#print axioms neighbor_patterns_of_global_shape
end SpectreFinite.HexSearch.ParentBoundary
