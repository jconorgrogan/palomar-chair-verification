module

public import SpectreFinite.ParentBoundaryNativeBinding
public import SpectreFinite.ChildBoundaryWitness

@[expose] public section


/-! Actual adjacent native cells either have the same parent or cross one
of its six proved macro-sides. No connectedness or coarse-chart premise. -/
namespace SpectreFinite.HexSearch.NativeCoarse
open ParentOwnership ParentBoundary Boundary

theorem parentCell_child_witness (f : Position → State)
    (a : Anchor f) (k : TileKind) (hk : ExactParentAt f a.val k)
    (x : Position) (hx : ParentCell f a.val x) :
    ∃ c ∈ children k, x = addPos a.val (rotatePosition (f a.val).2 (pos c)) := by
  have hm := (hk x (f x)).mp ⟨hx,rfl⟩
  obtain ⟨e,he,heq⟩ := List.mem_map.mp hm
  obtain ⟨c,hc,hce⟩ := List.mem_map.mp he
  refine ⟨c,hc,?_⟩
  have hh := congrArg Prod.fst heq
  rw [← hce] at hh
  exact hh.symm

theorem parentCell_of_child (f : Position → State) (a : Anchor f)
    (k : TileKind) (hk : ExactParentAt f a.val k)
    (c : PlacedHex) (hc : c ∈ children k) :
    ParentCell f a.val (addPos a.val (rotatePosition (f a.val).2 (pos c))) := by
  have hm : (pos c,(c.kind,c.turn)) ∈ childPatch k := List.mem_map.mpr ⟨c,hc,rfl⟩
  have hp := (mem_framedChildPatch_iff f a.val k (pos c) (c.kind,c.turn)).mpr hm
  exact ((hk _ _).mpr hp).1

/-- This uses complete parent shapes and the proved native boundary partition,
not a postulated contact graph. -/
theorem adjacent_parent_eq_or_neighbor (f : Position → State) (h : Recognition f)
    (hc : ∀ a : Anchor f, FramedRootStructure (normalizedAt f a.val))
    (a b : Anchor f) (x : Position) (d : Fin 6)
    (ha : ParentCell f a.val x) (hb : ParentCell f b.val (addPos x (direction d))) :
    b = a ∨ ∃ s : Fin 6, b = neighbor f h s a := by
  classical
  by_cases heq : b = a
  · exact Or.inl heq
  right
  obtain ⟨k,ns,frames,hp,hstruct,hgeom,hrows⟩ := hc a
  have hk := exactParentAt_of_rootParent f a.val a.property k hp
  obtain ⟨c,hcm,hx⟩ := parentCell_child_witness f a k hk x ha
  let t := (f a.val).2
  let eDir := rotateTurn (inverseTurn t) d
  have hy : addPos x (direction d) =
      addPos a.val (rotatePosition t (addPos (pos c) (direction eDir))) := by
    rw [rotatePosition_add,rotatePosition_direction,rotateTurn_inverse_right]
    rw [← addPos_assoc]
    exact congrArg (fun p => addPos p (direction d)) hx
  have hex : ExposedChildEdge k c eDir := by
    intro c' hc' hcpos
    have hown := parentCell_of_child f a k hk c' hc'
    rw [hcpos,← hy] at hown
    have he := parent_cells_disjoint f h.unique _ _ _ hb hown
    exact heq (Subtype.ext he)
  obtain ⟨s,e,hem,hec,hed⟩ := exposed_child_macro_side k c hcm eDir hex
  refine ⟨rotateTurn t s,?_⟩
  have hs : rotateTurn (inverseTurn (f a.val).2) (rotateTurn t s) = s :=
    rotateTurn_inverse t s
  have hown := neighbor_owns_segment_cell f h a k ns hp hstruct (rotateTurn t s) e
    (by simpa only [hs] using hem)
  have houtside : outsideCell k e = addPos (pos c) (direction eDir) := by
    simp only [outsideCell,hec,hed]
  rw [houtside,← hy] at hown
  exact Subtype.ext (parent_cells_disjoint f h.unique _ _ _ hb hown)

noncomputable def owner (f : Position → State) (h : Recognition f) (x : Position) : Anchor f :=
  ⟨parentAnchor f h.unique x,parentAnchor_gamma f h.unique x⟩

theorem owner_spec (f : Position → State) (h : Recognition f) (x : Position) :
    ParentCell f (owner f h x).val x := parentAnchor_spec f h.unique x

theorem owner_self (f : Position → State) (h : Recognition f) (a : Anchor f) :
    owner f h a.val = a := Subtype.ext (parentAnchor_self f h.unique a.val a.property)

theorem adjacent_owner_eq_or_neighbor (f : Position → State) (h : Recognition f)
    (hc : ∀ a : Anchor f, FramedRootStructure (normalizedAt f a.val))
    (x : Position) (d : Fin 6) :
    owner f h (addPos x (direction d)) = owner f h x ∨
      ∃ s : Fin 6, owner f h (addPos x (direction d)) = neighbor f h s (owner f h x) :=
  adjacent_parent_eq_or_neighbor f h hc _ _ x d (owner_spec f h x) (owner_spec f h _)

end SpectreFinite.HexSearch.NativeCoarse
