module

public import SpectreFinite.ParentBoundaryNativeMating

@[expose] public section


/-! Opposite inverses and triangular steps of the actual native-owner neighbor
function. The universal normalized finite certificate remains explicit. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary NativeCoarse

theorem actualSegment_of_local_frame (f : Position → State) (h : Recognition f)
    (a : Anchor f) (k : TileKind) (ns : List Position) (frames : List FrameInfo)
    (hp : rootParent (normalizedAt f a.val) = childPatch k)
    (hb : Structure (owners (normalizedAt f a.val)) k ns)
    (hg : FrameGeometry k ns frames) (hr : FrameRows (normalizedAt f a.val) frames)
    (s u : Fin 6) :
    placedSegment (parentKind f h (neighbor f h (rotateTurn (f a.val).2 s) a))
      (neighbor f h (rotateTurn (f a.val).2 s) a).val
      (f (neighbor f h (rotateTurn (f a.val).2 s) a).val).2 u =
      (frameSegment (frameAt frames s) u).map (moveSide a.val (f a.val).2) := by
  rw [neighbor_kind_of_frame f h a k ns frames hp hb hg hr,
      neighbor_state_of_frame f h a k ns frames hp hb hg hr,
      neighbor_value_of_frame f h a k ns frames hp hb hg]
  simp only [rotateTurn_inverse]
  exact (moveSide_segment a.val _ (f a.val).2 _ _ u).symm

theorem neighbor_turn_local (f : Position → State) (h : Recognition f)
    (a : Anchor f) (k : TileKind) (ns : List Position) (frames : List FrameInfo)
    (hp : rootParent (normalizedAt f a.val) = childPatch k)
    (hb : Structure (owners (normalizedAt f a.val)) k ns)
    (hg : FrameGeometry k ns frames) (hr : FrameRows (normalizedAt f a.val) frames)
    (s : Fin 6) :
    (f (neighbor f h (rotateTurn (f a.val).2 s) a).val).2 =
      rotateTurn (f a.val).2 (frameAt frames s).turn := by
  have hs := congrArg Prod.snd (neighbor_state_of_frame f h a k ns frames hp hb hg hr
    (rotateTurn (f a.val).2 s))
  simpa only [rotateTurn_inverse] using hs

theorem neighbor_opposite_of_frame (f : Position → State) (h : Recognition f)
    (a : Anchor f) (k : TileKind) (ns : List Position) (frames : List FrameInfo)
    (hp : rootParent (normalizedAt f a.val) = childPatch k)
    (hb : Structure (owners (normalizedAt f a.val)) k ns)
    (hg : FrameGeometry k ns frames) (hr : FrameRows (normalizedAt f a.val) frames)
    (s : Fin 6) :
    neighbor f h (opposite (rotateTurn (f a.val).2 s))
      (neighbor f h (rotateTurn (f a.val).2 s) a) = a := by
  have hk := parentKind_unique f h a k
    (exactParentAt_of_rootParent f a.val a.property k hp)
  apply neighbor_of_mating f h a _ s (frameAt frames s).mateSide
  · rw [neighbor_turn_local f h a k ns frames hp hb hg hr,
        ← rotateTurn_assoc]
    rw [show rotateTurn (frameAt frames s).turn (frameAt frames s).mateSide = opposite s
      from (hg.2.2.2.1 s).2.2]
    exact rotateTurn_opposite (f a.val).2 s
  · rw [actualSegment_of_local_frame f h a k ns frames hp hb hg hr,
        (hg.2.2.2.1 s).1,moveSide_mating,moveSide_segment_origin,hk]

private theorem pred_next : ∀ s : Fin 6, rotateTurn 5 (rotateTurn 1 s) = s := by decide
private theorem shift_comm : ∀ t r s : Fin 6,
    rotateTurn t (rotateTurn r s) = rotateTurn r (rotateTurn t s) := by decide

theorem neighbor_triangle_of_frame (f : Position → State) (h : Recognition f)
    (a : Anchor f) (k : TileKind) (ns : List Position) (frames : List FrameInfo)
    (hp : rootParent (normalizedAt f a.val) = childPatch k)
    (hb : Structure (owners (normalizedAt f a.val)) k ns)
    (hg : FrameGeometry k ns frames) (hr : FrameRows (normalizedAt f a.val) frames)
    (s : Fin 6) :
    neighbor f h (rotateTurn 2 (rotateTurn (f a.val).2 s))
      (neighbor f h (rotateTurn (f a.val).2 s) a) =
      neighbor f h (rotateTurn (f a.val).2 (rotateTurn 1 s)) a := by
  have ht := hg.2.2.2.2 (rotateTurn 1 s)
  dsimp only at ht
  rw [pred_next] at ht
  apply neighbor_of_mating f h _ _
    (rotateTurn 1 (frameAt frames (rotateTurn 1 s)).mateSide)
    (rotateTurn 5 (frameAt frames s).mateSide)
  · rw [neighbor_turn_local f h a k ns frames hp hb hg hr, ← rotateTurn_assoc]
    rw [show rotateTurn (frameAt frames s).turn (rotateTurn 5 (frameAt frames s).mateSide) =
        rotateTurn 1 (rotateTurn 1 s) from ht.2.2.1]
    have htwo : ∀ s : Fin 6, rotateTurn 1 (rotateTurn 1 s) = rotateTurn 2 s := by decide
    rw [htwo,shift_comm]
  · rw [actualSegment_of_local_frame f h a k ns frames hp hb hg hr,
        actualSegment_of_local_frame f h a k ns frames hp hb hg hr]
    have hm := congrArg (fun es => es.map (moveSide a.val (f a.val).2)) ht.1
    rw [moveSide_mating] at hm
    rw [hm,matingSegment_involutive]

/-- These hypotheses contain only recognition of actual parents and the
proved local finite boundary/frame certificate at each normalized Gamma. -/
theorem neighbor_opposite_inverse (f : Position → State) (h : Recognition f)
    (hc : ∀ a : Anchor f, FramedRootStructure (normalizedAt f a.val)) :
    ∀ d : Fin 6, ∀ a : Anchor f, neighbor f h (opposite d) (neighbor f h d a) = a := by
  intro d a
  obtain ⟨k,ns,frames,hp,hb,hg,hr⟩ := hc a
  have he := neighbor_opposite_of_frame f h a k ns frames hp hb hg hr
    (rotateTurn (inverseTurn (f a.val).2) d)
  simpa only [rotateTurn_inverse_right] using he

theorem neighbor_triangle (f : Position → State) (h : Recognition f)
    (hc : ∀ a : Anchor f, FramedRootStructure (normalizedAt f a.val)) :
    ∀ d : Fin 6, ∀ a : Anchor f,
      neighbor f h (rotateTurn 2 d) (neighbor f h d a) =
        neighbor f h (rotateTurn 1 d) a := by
  intro d a
  obtain ⟨k,ns,frames,hp,hb,hg,hr⟩ := hc a
  have he := neighbor_triangle_of_frame f h a k ns frames hp hb hg hr
    (rotateTurn (inverseTurn (f a.val).2) d)
  rw [shift_comm (f a.val).2 1] at he
  simpa only [rotateTurn_inverse_right] using he

#print axioms actualSegment_of_local_frame
#print axioms neighbor_turn_local
#print axioms neighbor_opposite_of_frame
#print axioms neighbor_triangle_of_frame
#print axioms neighbor_opposite_inverse
#print axioms neighbor_triangle
end SpectreFinite.HexSearch.ParentBoundary
