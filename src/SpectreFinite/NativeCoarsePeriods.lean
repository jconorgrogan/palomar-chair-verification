module

public import SpectreFinite.NativeCoarseCoordinates

@[expose] public section


/-! Every actual fine-field period induces a literal period of the derived
coarse field. It also transports complete parent fibers exactly. No period
preservation premise is placed in the recognition interface. -/
namespace SpectreFinite.HexSearch.NativeCoarse
open ParentOwnership ParentBoundary

variable (f : Position → State) (h : Recognition f)
  (hc : ∀ a : Anchor f, FramedRootStructure (normalizedAt f a.val))

noncomputable def coarsePeriod (v : Position) (hv : FieldPeriod f v) : Position :=
  coordinate f h hc (translateAnchor f v hv (owner f h (0,0)))

theorem translateAnchor_translate (v : Position) (hv : FieldPeriod f v)
    (x : Position) (a : Anchor f) :
    translateAnchor f v hv ((stepSystem f h hc).translate x a) =
      (stepSystem f h hc).translate x (translateAnchor f v hv a) := by
  apply HexStepSystem.map_translate
  intro d a
  exact (neighbor_period f h v hv a d).symm

theorem anchorAt_period (v : Position) (hv : FieldPeriod f v) (x : Position) :
    anchorAt f h hc (addPos (coarsePeriod f h hc v hv) x) =
      translateAnchor f v hv (anchorAt f h hc x) := by
  have hr := anchorAt_coordinate f h hc (translateAnchor f v hv (owner f h (0,0)))
  change anchorAt f h hc (coarsePeriod f h hc v hv) = _ at hr
  unfold anchorAt at hr ⊢
  rw [reflectPosition_add]
  have he : addPos (reflectPosition (coarsePeriod f h hc v hv)) (reflectPosition x) =
      addPos (reflectPosition x) (reflectPosition (coarsePeriod f h hc v hv)) := by
    apply Prod.ext <;> simp only [addPos] <;> omega
  rw [he,HexStepSystem.translate_add,hr,translateAnchor_translate]

theorem coarsePeriod_spec (v : Position) (hv : FieldPeriod f v) :
    FieldPeriod (coarseField f h hc) (coarsePeriod f h hc v hv) := by
  intro x
  unfold coarseField
  rw [anchorAt_period,coarseState_period]

noncomputable def coordinateFiber (x : Position) : List Position := fiber f h (anchorAt f h hc x)

theorem mem_coordinateFiber_period (v : Position) (hv : FieldPeriod f v)
    (x p : Position) :
    addPos v p ∈ coordinateFiber f h hc (addPos (coarsePeriod f h hc v hv) x) ↔
      p ∈ coordinateFiber f h hc x := by
  unfold coordinateFiber
  rw [mem_fiber_iff,mem_fiber_iff,anchorAt_period]
  exact parentCell_period_iff f v hv _ p

theorem coordinateFiber_period (v : Position) (hv : FieldPeriod f v) (x : Position) :
    coordinateFiber f h hc (addPos (coarsePeriod f h hc v hv) x) =
      (coordinateFiber f h hc x).map (addPos v) := by
  unfold coordinateFiber
  rw [anchorAt_period]
  unfold fiber
  rw [parentKind_period]
  simp only [translateAnchor]
  unfold parentPositions
  rw [framedChildPatch_period f v hv]
  simp only [List.map_map]
  rfl

theorem coordinateFiber_disjoint (x y p : Position)
    (hx : p ∈ coordinateFiber f h hc x) (hy : p ∈ coordinateFiber f h hc y) : x = y := by
  apply anchorAt_injective f h hc
  apply Subtype.ext
  exact parent_cells_disjoint f h.unique _ _ p
    ((mem_fiber_iff f h _ p).mp hx) ((mem_fiber_iff f h _ p).mp hy)

theorem coordinateFiber_cover (p : Position) :
    ∃ x, p ∈ coordinateFiber f h hc x := by
  refine ⟨coordinate f h hc (owner f h p),?_⟩
  unfold coordinateFiber
  rw [anchorAt_coordinate]
  exact (mem_fiber_iff f h _ p).mpr (owner_spec f h p)

end SpectreFinite.HexSearch.NativeCoarse
