module

public import SpectreFinite.ParentSizes
public import SpectreFinite.BoundaryGrowth
public import SpectreFinite.ParentBoundary

@[expose] public section


/-! Coarse neighbors are defined from the actual native-cell owner algorithm,
not supplied as a graph. The recognition record is an explicit intermediate
interface; its constructor from global legality is provided only after the
complete finite occurrence chain. No inverse/triangle law is assumed here. -/
namespace SpectreFinite.HexSearch.NativeCoarse
open ParentOwnership Boundary ParentBoundary

structure Recognition (f : Position → State) : Prop where
  unique : ∀ x, UniqueAt f x
  shapes : ∀ a, (f a).1 = 0 → ∃ k, ExactParentAt f a k

abbrev Anchor (f : Position → State) := {a : Position // (f a).1 = 0}

noncomputable def parentKind (f : Position → State) (h : Recognition f) (a : Anchor f) : TileKind :=
  Classical.choose (h.shapes a.val a.property)

theorem parentKind_spec (f : Position → State) (h : Recognition f) (a : Anchor f) :
    ExactParentAt f a.val (parentKind f h a) := Classical.choose_spec (h.shapes a.val a.property)

theorem parentKind_unique (f : Position → State) (h : Recognition f) (a : Anchor f)
    (k : TileKind) (hk : ExactParentAt f a.val k) : k = parentKind f h a :=
  exactParentAt_kind_unique f a.val k _ hk (parentKind_spec f h a)

def firstSide (k : TileKind) (s : Fin 6) : SideRef :=
  match segment k s with
  | [] => ⟨0,0⟩
  | e::_ => e

theorem firstSide_mem (k : TileKind) (s : Fin 6) : firstSide k s ∈ segment k s := by
  have hb := (segment_length_bounds k s).1
  cases he : segment k s with
  | nil => simp only [he,List.length_nil] at hb; omega
  | cons e es => simp [firstSide,he]

noncomputable def outsideQuery (f : Position → State) (h : Recognition f)
    (a : Anchor f) (d : Fin 6) : Position :=
  let k := parentKind f h a
  let t := (f a.val).2
  let s := rotateTurn (inverseTurn t) d
  addPos a.val (rotatePosition t (outsideCell k (firstSide k s)))

noncomputable def neighbor (f : Position → State) (h : Recognition f)
    (d : Fin 6) (a : Anchor f) : Anchor f :=
  ⟨parentAnchor f h.unique (outsideQuery f h a d),
    parentAnchor_gamma f h.unique (outsideQuery f h a d)⟩

theorem neighbor_selected (f : Position → State) (h : Recognition f)
    (d : Fin 6) (a : Anchor f) :
    ParentCell f (neighbor f h d a).val (outsideQuery f h a d) :=
  parentAnchor_spec f h.unique (outsideQuery f h a d)

theorem neighbor_eq_of_selected (f : Position → State) (h : Recognition f)
    (d : Fin 6) (a b : Anchor f)
    (hb : ParentCell f b.val (outsideQuery f h a d)) : neighbor f h d a = b := by
  apply Subtype.ext
  exact parent_cells_disjoint f h.unique _ _ _ (neighbor_selected f h d a) hb

def translateAnchor (f : Position → State) (v : Position) (hv : FieldPeriod f v)
    (a : Anchor f) : Anchor f := ⟨addPos v a.val,by rw [hv a.val]; exact a.property⟩

theorem parentKind_period (f : Position → State) (h : Recognition f)
    (v : Position) (hv : FieldPeriod f v) (a : Anchor f) :
    parentKind f h (translateAnchor f v hv a) = parentKind f h a := by
  symm
  exact parentKind_unique f h _ _
    (exactParentAt_period f v hv a.val _ (parentKind_spec f h a))

theorem outsideQuery_period (f : Position → State) (h : Recognition f)
    (v : Position) (hv : FieldPeriod f v) (a : Anchor f) (d : Fin 6) :
    outsideQuery f h (translateAnchor f v hv a) d = addPos v (outsideQuery f h a d) := by
  simp only [outsideQuery]
  rw [parentKind_period]
  simp only [translateAnchor,hv a.val]
  exact addPos_assoc v a.val _

/-- The actual coarse-neighbor rule commutes with every literal fine-field
period; this is derived rather than stored in Recognition. -/
theorem neighbor_period (f : Position → State) (h : Recognition f)
    (v : Position) (hv : FieldPeriod f v) (a : Anchor f) (d : Fin 6) :
    neighbor f h d (translateAnchor f v hv a) = translateAnchor f v hv (neighbor f h d a) := by
  apply Subtype.ext
  change parentAnchor f h.unique (outsideQuery f h (translateAnchor f v hv a) d) =
    addPos v (parentAnchor f h.unique (outsideQuery f h a d))
  rw [outsideQuery_period,parentAnchor_period f h.unique v hv]

noncomputable def coarseState (f : Position → State) (h : Recognition f) (a : Anchor f) : State :=
  (parentKind f h a,inverseTurn (f a.val).2)

theorem coarseState_period (f : Position → State) (h : Recognition f)
    (v : Position) (hv : FieldPeriod f v) (a : Anchor f) :
    coarseState f h (translateAnchor f v hv a) = coarseState f h a := by
  unfold coarseState
  rw [parentKind_period]
  simp only [translateAnchor,hv a.val]

end SpectreFinite.HexSearch.NativeCoarse
