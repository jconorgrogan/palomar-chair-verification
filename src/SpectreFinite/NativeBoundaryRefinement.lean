module

public import SpectreFinite.NativeCoarseCoordinates

@[expose] public section


/-! Each actual coarse edge expands to its literal native boundary segment.
Every edge exposed by a finite union of complete parent fibers is covered by
an exposed coarse edge, using actual neighbor ownership rather than a supplied
boundary-completeness premise. -/
namespace SpectreFinite.HexSearch.NativeBoundaryRefinement
open ParentOwnership ParentBoundary Boundary NativeCoarse

abbrev Edge := Position × Fin 6

def Exposed (A : List Position) (e : Edge) : Prop :=
  e.1 ∈ A ∧ addPos e.1 (direction e.2) ∉ A

variable (f : Position → State) (h : Recognition f)
  (hc : ∀ a : Anchor f, FramedRootStructure (normalizedAt f a.val))

noncomputable def refine (A : List Position) : List Position :=
  A.flatMap fun x => fiber f h (anchorAt f h hc x)

theorem mem_refine_iff (A : List Position) (p : Position) :
    p ∈ refine f h hc A ↔ ∃ x ∈ A, ParentCell f (anchorAt f h hc x).val p := by
  simp only [refine,List.mem_flatMap,mem_fiber_iff]

def framedEdge (f : Position → State) (a : Anchor f) (k : TileKind)
    (e : SideRef) : Edge :=
  (addPos a.val (rotatePosition (f a.val).2 (pos (hexAt (children k) e))),
    rotateTurn (f a.val).2 e.side)

noncomputable def expansion (e : Edge) : List Edge :=
  let a := anchorAt f h hc e.1
  let k := parentKind f h a
  let s := rotateTurn (inverseTurn (f a.val).2) (inverseTurn e.2)
  (segment k s).map (framedEdge f a k)

theorem expansion_length_le (e : Edge) : (expansion f h hc e).length ≤ 6 := by
  simp only [expansion,List.length_map]
  exact (segment_length_bounds _ _).2


/-- Every expanded edge starts in its actual coarse parent fiber. -/
theorem expansion_inside_parent (e b : Edge) (hb : b ∈ expansion f h hc e) :
    ParentCell f (anchorAt f h hc e.1).val b.1 := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
  exact parentCell_of_child f _ _ (parentKind_spec f h _) _
    (segment_hexAt_mem _ _ v hv)

/-- Its opposite cell is owned by the actual parent at the adjacent coarse
coordinate, for every literal child side in the entire macro-side. -/
theorem expansion_outside_parent (e b : Edge) (hb : b ∈ expansion f h hc e) :
    ParentCell f (anchorAt f h hc (addPos e.1 (direction e.2))).val
      (addPos b.1 (direction b.2)) := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
  let a := anchorAt f h hc e.1
  obtain ⟨k,ns,frames,hp,hstruct,hgeom,hrows⟩ := hc a
  have hk := parentKind_unique f h a k
    (exactParentAt_of_rootParent f a.val a.property k hp)
  subst k
  have ho := neighbor_owns_segment_cell f h a _ ns hp hstruct (inverseTurn e.2) v hv
  rw [anchorAt_direction]
  change ParentCell f (neighbor f h (inverseTurn e.2) a).val
    (addPos (addPos a.val (rotatePosition (f a.val).2
      (pos (hexAt (children (parentKind f h a)) v))))
      (direction (rotateTurn (f a.val).2 v.side)))
  rw [← rotatePosition_direction,addPos_assoc,← rotatePosition_add]
  exact ho

/-- Coarse exposed edges expand only to genuinely exposed native edges.
The proof uses unique native ownership and injectivity of the constructed
coarse chart to exclude every other selected parent. -/
theorem expansion_exposed (A : List Position) (e b : Edge)
    (he : Exposed A e) (hb : b ∈ expansion f h hc e) :
    Exposed (refine f h hc A) b := by
  refine ⟨(mem_refine_iff f h hc A _).mpr
    ⟨e.1,he.1,expansion_inside_parent f h hc e b hb⟩,?_⟩
  intro hbin
  obtain ⟨x,hx,hown⟩ := (mem_refine_iff f h hc A _).mp hbin
  have ha := parent_cells_disjoint f h.unique _ _ _
    (expansion_outside_parent f h hc e b hb) hown
  have heq := anchorAt_injective f h hc (Subtype.ext ha)
  exact he.2 (heq.symm ▸ hx)

/-- The segment chart is oriented in the actual native frame. The reflected
coarse direction is converted back before selecting the macro-side. -/
theorem exposed_refine_covered (A : List Position) (p : Position) (d : Fin 6)
    (hexposed : Exposed (refine f h hc A) (p,d)) :
    ∃ e : Edge, Exposed A e ∧ (p,d) ∈ expansion f h hc e := by
  classical
  obtain ⟨x,hx,hown⟩ := (mem_refine_iff f h hc A p).mp hexposed.1
  let a := anchorAt f h hc x
  let t := (f a.val).2
  obtain ⟨k,ns,frames,hp,hstruct,hgeom,hrows⟩ := hc a
  have hk := exactParentAt_of_rootParent f a.val a.property k hp
  have hkind : k = parentKind f h a := parentKind_unique f h a k hk
  obtain ⟨c,hcm,hpchild⟩ := parentCell_child_witness f a k hk p hown
  let childDir := rotateTurn (inverseTurn t) d
  have hnext : addPos p (direction d) =
      addPos a.val (rotatePosition t (addPos (pos c) (direction childDir))) := by
    rw [rotatePosition_add,rotatePosition_direction,rotateTurn_inverse_right]
    rw [← addPos_assoc]
    exact congrArg (fun q => addPos q (direction d)) hpchild
  have hchild : ExposedChildEdge k c childDir := by
    intro c' hc' hpos
    have hinside := parentCell_of_child f a k hk c' hc'
    rw [hpos,← hnext] at hinside
    exact hexposed.2 ((mem_refine_iff f h hc A _).mpr ⟨x,hx,hinside⟩)
  obtain ⟨s,b,hbs,hbc,hbd⟩ := exposed_child_macro_side k c hcm childDir hchild
  let coarseDir := inverseTurn (rotateTurn t s)
  have hdir : inverseTurn coarseDir = rotateTurn t s := inverseTurn_involutive _
  have hside : rotateTurn (inverseTurn (f a.val).2) (inverseTurn coarseDir) = s := by
    rw [hdir]
    exact rotateTurn_inverse t s
  have hneighbor := neighbor_owns_segment_cell f h a k ns hp hstruct
    (inverseTurn coarseDir) b (by simpa only [hside] using hbs)
  have houtside : outsideCell k b = addPos (pos c) (direction childDir) := by
    simp only [outsideCell,hbc,hbd]
  rw [houtside,← hnext] at hneighbor
  refine ⟨(x,coarseDir),⟨hx,?_⟩,?_⟩
  · intro hxin
    apply hexposed.2
    apply (mem_refine_iff f h hc A _).mpr
    refine ⟨addPos x (direction coarseDir),hxin,?_⟩
    rw [anchorAt_direction]
    exact hneighbor
  · change (p,d) ∈ (segment (parentKind f h a)
      (rotateTurn (inverseTurn (f a.val).2) (inverseTurn coarseDir))).map _
    rw [hside,← hkind]
    apply List.mem_map.mpr
    refine ⟨b,hbs,?_⟩
    apply Prod.ext
    · change addPos a.val (rotatePosition t (pos (hexAt (children k) b))) = p
      rw [hbc]
      exact hpchild.symm
    · change rotateTurn t b.side = d
      rw [hbd]
      exact rotateTurn_inverse_right t d

/-- Exact native-boundary refinement, with neither missing nor spurious
expanded edges. -/
theorem exposed_refine_iff (A : List Position) (b : Edge) :
    Exposed (refine f h hc A) b ↔
      ∃ e : Edge, Exposed A e ∧ b ∈ expansion f h hc e := by
  constructor
  · exact exposed_refine_covered f h hc A b.1 b.2
  · rintro ⟨e,he,hb⟩
    exact expansion_exposed f h hc A e b he hb

end SpectreFinite.HexSearch.NativeBoundaryRefinement
