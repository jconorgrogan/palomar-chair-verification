module

public import SpectreFinite.ParentBoundaryNativeBinding

@[expose] public section


/-! Identifying the certified neighboring kind with its actual complete
parent kind. Only actual child values are transported through affine frames;
a bounded candidate is never defined to be the complete parent. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary NativeCoarse

/-- Complete actual parent recognition supplies every literal child value. -/
theorem exactParentAt_child_value (f : Position → State) (a : Position)
    (j : TileKind) (hp : ExactParentAt f a j) (c : PlacedHex) (hc : c ∈ children j) :
    f (addPos a (rotatePosition (f a).2 (pos c))) =
      rotateState (f a).2 (c.kind,c.turn) := by
  have hm : (pos c,(c.kind,c.turn)) ∈ childPatch j :=
    List.mem_map.mpr ⟨c,hc,rfl⟩
  exact ((hp _ _).mpr ((mem_framedChildPatch_iff f a j _ _).mpr hm)).2.symm

/-- Actual child values in a composite native frame pass the displayed
child-agreement test in the outer normalized frame. -/
theorem childAgreement_of_affine_exactParent (f : Position → State)
    (center a : Position) (t u : Fin 6) (j : TileKind)
    (ht : (f (addPos center (rotatePosition t a))).2 = rotateTurn t u)
    (hp : ExactParentAt f (addPos center (rotatePosition t a)) j) :
    ChildAgreement (rotatedField (inverseTurn t) (shiftedField f center)) a u j := by
  intro c hc _
  have hv := exactParentAt_child_value f _ j hp c hc
  rw [ht] at hv
  have hx : addPos (addPos center (rotatePosition t a))
      (rotatePosition (rotateTurn t u) (pos c)) =
      addPos center (rotatePosition t (placedPosition a u c)) := by
    rw [placedPosition, rotatePosition_add, ← rotatePosition_comp]
    exact addPos_assoc center (rotatePosition t a) _
  rw [hx, normalized_field_value f center t, ← rotateState_comp] at hv
  exact rotateState_injective t _ _ hv

/-- Recognition supplies the actual complete neighboring parent. Its child
states pass the certified unique candidate test, discharging the kind binding. -/
theorem neighbor_kind_of_frame (f : Position → State) (h : Recognition f)
    (a : Anchor f) (k : TileKind) (ns : List Position) (frames : List FrameInfo)
    (hp : rootParent (normalizedAt f a.val) = childPatch k)
    (hb : Structure (owners (normalizedAt f a.val)) k ns)
    (hg : FrameGeometry k ns frames)
    (hr : FrameRows (normalizedAt f a.val) frames) (d : Fin 6) :
    parentKind f h (neighbor f h d a) =
      (frameAt frames (rotateTurn (inverseTurn (f a.val).2) d)).kind := by
  let s := rotateTurn (inverseTurn (f a.val).2) d
  let n := frameAt frames s
  have hn : (neighbor f h d a).val = addPos a.val (rotatePosition (f a.val).2 n.anchor) :=
    neighbor_value_of_frame f h a k ns frames hp hb hg d
  have hs : f (addPos a.val (rotatePosition (f a.val).2 n.anchor)) =
      (0,rotateTurn (f a.val).2 n.turn) := by
    rw [← hn]
    exact neighbor_state_of_frame f h a k ns frames hp hb hg hr d
  have he := parentKind_spec f h (neighbor f h d a)
  rw [hn] at he
  have hc := childAgreement_of_affine_exactParent f a.val n.anchor (f a.val).2
    n.turn (parentKind f h (neighbor f h d a)) (congrArg Prod.snd hs) he
  have hm := (mem_matchingKinds_iff (normalizedAt f a.val) n.anchor n.turn _).mpr hc
  rw [(hr s).2] at hm
  simpa only [List.mem_singleton] using hm

#print axioms exactParentAt_child_value
#print axioms childAgreement_of_affine_exactParent
#print axioms neighbor_kind_of_frame
end SpectreFinite.HexSearch.ParentBoundary
