module

public import SpectreFinite.ParentBoundaryFrameTransfer
public import SpectreFinite.NativeCoarseNeighbors

@[expose] public section


/-! The finite normalized boundary witnesses bind to neighbors defined from
actual native-cell ownership. Recognition contains no coarse graph laws. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary NativeCoarse

private theorem anchor_getD (frames : List FrameInfo) (i : Nat) :
    ((frames.getD i defaultFrame).anchor) =
      (frames.map FrameInfo.anchor).getD i (0,0) := by
  induction frames generalizing i with
  | nil => simp [List.getD, defaultFrame]
  | cons a as ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem frameAt_anchor (k : TileKind) (ns : List Position) (frames : List FrameInfo)
    (hg : FrameGeometry k ns frames) (s : Fin 6) :
    (frameAt frames s).anchor = ns.getD s.val (0,0) := by
  rw [frameAt, anchor_getD, hg.2.1]

/-- Every side of the certified normalized segment selects the actual affine
neighbor, so the arbitrary first-side choice does not change that neighbor. -/
theorem neighbor_value_of_structure (f : Position → State) (h : Recognition f)
    (a : Anchor f) (k : TileKind) (ns : List Position)
    (hp : rootParent (normalizedAt f a.val) = childPatch k)
    (hb : Structure (owners (normalizedAt f a.val)) k ns) (d : Fin 6) :
    (neighbor f h d a).val = addPos a.val (rotatePosition (f a.val).2
      (ns.getD (rotateTurn (inverseTurn (f a.val).2) d).val (0,0))) := by
  have hk := parentKind_unique f h a k
    (exactParentAt_of_rootParent f a.val a.property k hp)
  let s := rotateTurn (inverseTurn (f a.val).2) d
  have ho := hb.2.2.2.1 s (firstSide k s) (firstSide_mem k s)
  have hm : ns.getD s.val (0,0) ∈
      owners (normalizedAt f a.val) (outsideCell k (firstSide k s)) := by
    rw [ho]
    simp
  have ha := (mem_owners_shift_rotate_iff f a.val (f a.val).2
    (outsideCell k (firstSide k s)) (ns.getD s.val (0,0))).mpr hm
  change parentAnchor f h.unique (outsideQuery f h a d) = _
  apply (parentAnchor_eq_iff f h.unique _ _).mpr
  change _ ∈ owners f (outsideQuery f h a d)
  simpa only [outsideQuery, ← hk] using ha

/-- Choosing any native side in the macro-side selects the same actual
neighbor, not only the first native side used by outsideQuery. -/
theorem neighbor_owns_segment_cell (f : Position → State) (h : Recognition f)
    (a : Anchor f) (k : TileKind) (ns : List Position)
    (hp : rootParent (normalizedAt f a.val) = childPatch k)
    (hb : Structure (owners (normalizedAt f a.val)) k ns)
    (d : Fin 6) (e : SideRef)
    (he : e ∈ segment k (rotateTurn (inverseTurn (f a.val).2) d)) :
    ParentCell f (neighbor f h d a).val
      (addPos a.val (rotatePosition (f a.val).2 (outsideCell k e))) := by
  rw [neighbor_value_of_structure f h a k ns hp hb d]
  apply (mem_owners_shift_rotate_iff f a.val (f a.val).2 _ _).mpr
  change _ ∈ owners (normalizedAt f a.val) (outsideCell k e)
  rw [hb.2.2.2.1 _ e he]
  simp

/-- The table's anchor is exactly the actual coarse neighbor, in the root's
real position and turn frame. -/
theorem neighbor_value_of_frame (f : Position → State) (h : Recognition f)
    (a : Anchor f) (k : TileKind) (ns : List Position) (frames : List FrameInfo)
    (hp : rootParent (normalizedAt f a.val) = childPatch k)
    (hb : Structure (owners (normalizedAt f a.val)) k ns)
    (hg : FrameGeometry k ns frames) (d : Fin 6) :
    (neighbor f h d a).val = addPos a.val (rotatePosition (f a.val).2
      (frameAt frames (rotateTurn (inverseTurn (f a.val).2) d)).anchor) := by
  rw [frameAt_anchor k ns frames hg]
  exact neighbor_value_of_structure f h a k ns hp hb d

/-- FrameRows supplies the actual fine Gamma turn at the selected neighbor;
it is not a newly chosen or inferred coarse orientation. -/
theorem neighbor_state_of_frame (f : Position → State) (h : Recognition f)
    (a : Anchor f) (k : TileKind) (ns : List Position) (frames : List FrameInfo)
    (hp : rootParent (normalizedAt f a.val) = childPatch k)
    (hb : Structure (owners (normalizedAt f a.val)) k ns)
    (hg : FrameGeometry k ns frames)
    (hr : FrameRows (normalizedAt f a.val) frames) (d : Fin 6) :
    f (neighbor f h d a).val =
      (0,rotateTurn (f a.val).2
        (frameAt frames (rotateTurn (inverseTurn (f a.val).2) d)).turn) := by
  rw [neighbor_value_of_frame f h a k ns frames hp hb hg d]
  rw [normalized_field_value f a.val (f a.val).2]
  change rotateState (f a.val).2 (normalizedAt f a.val _) = _
  rw [(hr _).1]
  rfl

#print axioms frameAt_anchor
#print axioms neighbor_value_of_structure
#print axioms neighbor_owns_segment_cell
#print axioms neighbor_value_of_frame
#print axioms neighbor_state_of_frame
end SpectreFinite.HexSearch.ParentBoundary
