module

public import SpectreFinite.ParentBoundaryFrameAgreement

@[expose] public section


/-! Exact native-side mating implies equality of actual selected neighbors.
No topological cellulation or coarse graph hypothesis is used. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary NativeCoarse

def moveSide (a : Position) (t : Fin 6) (e : NativeSide) : NativeSide :=
  (addPos a (rotatePosition t e.1),rotateTurn t e.2)

theorem acrossSide_involutive (e : NativeSide) : acrossSide (acrossSide e) = e := by
  have hd : ∀ d : Fin 6, addPos (direction d) (direction (opposite d)) = (0,0) := by decide
  have ho : ∀ d : Fin 6, opposite (opposite d) = d := by decide
  apply Prod.ext
  · change addPos (addPos e.1 (direction e.2)) (direction (opposite e.2)) = e.1
    rw [addPos_assoc, hd]
    simp [addPos]
  · exact ho e.2

theorem moveSide_across (a : Position) (t : Fin 6) (e : NativeSide) :
    moveSide a t (acrossSide e) = acrossSide (moveSide a t e) := by
  apply Prod.ext
  · change addPos a (rotatePosition t (addPos e.1 (direction e.2))) =
      addPos (addPos a (rotatePosition t e.1)) (direction (rotateTurn t e.2))
    rw [rotatePosition_add, rotatePosition_direction, addPos_assoc]
  · exact rotateTurn_opposite t e.2

theorem moveSide_placedSide (a b : Position) (t u : Fin 6)
    (k : TileKind) (e : SideRef) :
    moveSide a t (placedSide k b u e) =
      placedSide k (addPos a (rotatePosition t b)) (rotateTurn t u) e := by
  apply Prod.ext
  · change addPos a (rotatePosition t (addPos b (rotatePosition u _))) = _
    rw [rotatePosition_add, rotatePosition_comp]
    exact (addPos_assoc a (rotatePosition t b) _).symm
  · exact rotateTurn_assoc t u e.side

theorem moveSide_segment (a b : Position) (t u : Fin 6) (k : TileKind) (s : Fin 6) :
    (placedSegment k b u s).map (moveSide a t) =
      placedSegment k (addPos a (rotatePosition t b)) (rotateTurn t u) s := by
  simp only [placedSegment,List.map_map]
  apply List.map_congr_left
  intro e _
  exact moveSide_placedSide a b t u k e

theorem moveSide_mating (a : Position) (t : Fin 6) (es : List NativeSide) :
    (matingSegment es).map (moveSide a t) =
      matingSegment (es.map (moveSide a t)) := by
  simp only [matingSegment,List.map_reverse,List.map_map]
  apply congrArg List.reverse
  apply List.map_congr_left
  intro e _
  exact moveSide_across a t e

theorem matingSegment_involutive (es : List NativeSide) :
    matingSegment (matingSegment es) = es := by
  simp [matingSegment,List.map_reverse,List.map_map,Function.comp_def,acrossSide_involutive]

theorem moveSide_segment_origin (a : Position) (t : Fin 6) (k : TileKind) (s : Fin 6) :
    (placedSegment k (0,0) 0 s).map (moveSide a t) = placedSegment k a t s := by
  have hz : ∀ t : Fin 6, rotateTurn t 0 = t := by decide
  rw [moveSide_segment,rotatePosition_zero,hz]
  simp [addPos]

theorem across_placedSide_position (k : TileKind) (a : Position) (t : Fin 6) (e : SideRef) :
    (acrossSide (placedSide k a t e)).1 = addPos a (rotatePosition t (outsideCell k e)) := by
  change addPos (addPos a (rotatePosition t (pos (hexAt (children k) e))))
      (direction (rotateTurn t e.side)) = _
  rw [outsideCell,rotatePosition_add,rotatePosition_direction,addPos_assoc]

theorem segment_hexAt_mem (k : TileKind) (s : Fin 6) (e : SideRef)
    (he : e ∈ segment k s) : hexAt (children k) e ∈ children k := by
  have hb := (nine_boundaries k).2.2.2.2.1 e ((mem_trace_iff_segment k e).mpr ⟨s,he⟩)
  apply List.mem_iff_getElem.mpr
  exact ⟨e.child,hb,by simp [hexAt,List.getD_eq_getElem?_getD,hb]⟩

theorem placedSegment_inside_parent (f : Position → State) (a : Position) (k : TileKind)
    (hp : ExactParentAt f a k) (s : Fin 6) (e : NativeSide)
    (he : e ∈ placedSegment k a (f a).2 s) : ParentCell f a e.1 := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
  let c := hexAt (children k) v
  have hc : c ∈ children k := segment_hexAt_mem k s v hv
  have hm : (pos c,(c.kind,c.turn)) ∈ childPatch k := List.mem_map.mpr ⟨c,hc,rfl⟩
  exact ((hp _ _).mpr ((mem_framedChildPatch_iff f a k _ _).mpr hm)).1

/-- Complete mating of native segments forces the actual selected neighbor.
The proof uses the first queried side and the actual parent of its across-cell. -/
theorem neighbor_of_mating (f : Position → State) (h : Recognition f)
    (a b : Anchor f) (sa sb d : Fin 6)
    (hd : rotateTurn (f b.val).2 sb = d)
    (hmate : placedSegment (parentKind f h b) b.val (f b.val).2 sb =
      matingSegment (placedSegment (parentKind f h a) a.val (f a.val).2 sa)) :
    neighbor f h d b = a := by
  let eb := placedSide (parentKind f h b) b.val (f b.val).2
    (firstSide (parentKind f h b) sb)
  have heb : eb ∈ placedSegment (parentKind f h b) b.val (f b.val).2 sb :=
    List.mem_map.mpr ⟨_,firstSide_mem _ sb,rfl⟩
  rw [hmate] at heb
  obtain ⟨ea,hea,hab⟩ := List.mem_map.mp heb
  have hea' : ea ∈ placedSegment (parentKind f h a) a.val (f a.val).2 sa :=
    List.mem_reverse.mp hea
  have hab' : acrossSide eb = ea := by
    rw [← hab, acrossSide_involutive]
  have hq : outsideQuery f h b d = (acrossSide eb).1 := by
    rw [← hd]
    simp only [outsideQuery,rotateTurn_inverse]
    exact (across_placedSide_position _ _ _ _).symm
  apply neighbor_eq_of_selected f h d b a
  rw [hq,hab']
  exact placedSegment_inside_parent f a.val _ (parentKind_spec f h a) sa ea hea'

#print axioms acrossSide_involutive
#print axioms moveSide_across
#print axioms moveSide_placedSide
#print axioms moveSide_segment
#print axioms moveSide_mating
#print axioms matingSegment_involutive
#print axioms moveSide_segment_origin
#print axioms across_placedSide_position
#print axioms segment_hexAt_mem
#print axioms placedSegment_inside_parent
#print axioms neighbor_of_mating
end SpectreFinite.HexSearch.ParentBoundary
