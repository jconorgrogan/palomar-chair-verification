module

public import SpectreFinite.NativeCoarseAdjacency
public import SpectreFinite.CoarseAddressBounds
public import SpectreFinite.CoarseActionFreeness
public import SpectreFinite.ParentBoundaryNeighborLabels

@[expose] public section


/-! The actual parent graph has global axial coordinates. The proof constructs
bounded native-path addresses and excludes nontrivial quotient periods by
quadratic native-cell growth versus linear growth modulo a kernel vector.
The explicit finite-occurrence inputs are Recognition and actual boundary
certificates; no free/transitive action or planar chart is supplied. -/
namespace SpectreFinite.HexSearch.NativeCoarse
open ParentOwnership ParentBoundary

variable (f : Position → State) (h : Recognition f)
  (hc : ∀ a : Anchor f, FramedRootStructure (normalizedAt f a.val))

noncomputable def stepSystem : HexStepSystem (Anchor f) where
  step := neighbor f h
  opposite_inverse := neighbor_opposite_inverse f h hc
  triangle := neighbor_triangle f h hc

noncomputable def rawAddress (x : Position) : Position :=
  boundedAddress (stepSystem f h hc) (owner f h) (adjacent_owner_eq_or_neighbor f h hc) x

theorem rawAddress_spec (x : Position) :
    owner f h x = (stepSystem f h hc).translate (rawAddress f h hc x) (owner f h (0,0)) :=
  (boundedAddress_spec (stepSystem f h hc) (owner f h)
    (adjacent_owner_eq_or_neighbor f h hc) x).2.2

theorem rawAddress_bound (n : Nat) (x : Position) (hx : x ∈ positiveSquare n) :
    (rawAddress f h hc x).1.natAbs ≤ 2*n ∧ (rawAddress f h hc x).2.natAbs ≤ 2*n :=
  boundedAddress_square (stepSystem f h hc) (owner f h)
    (adjacent_owner_eq_or_neighbor f h hc) n x hx

noncomputable def fiber (a : Anchor f) : List Position :=
  parentPositions f a.val (parentKind f h a)

theorem mem_fiber_iff (a : Anchor f) (x : Position) :
    x ∈ fiber f h a ↔ ParentCell f a.val x :=
  mem_parentPositions_iff f a.val _ (parentKind_spec f h a) x

theorem fiber_length_bounds (a : Anchor f) :
    7 ≤ (fiber f h a).length ∧ (fiber f h a).length ≤ 8 :=
  parentPositions_length_bounds f a.val _

theorem fiber_nodup (a : Anchor f) : (fiber f h a).Nodup :=
  parentPositions_nodup f a.val _

theorem rawAddress_cover (x : Position) :
    x ∈ fiber f h ((stepSystem f h hc).translate (rawAddress f h hc x) (owner f h (0,0))) := by
  rw [← rawAddress_spec f h hc x]
  exact (mem_fiber_iff f h _ x).mpr (owner_spec f h x)

theorem raw_orbit_injective :
    Function.Injective (fun x => (stepSystem f h hc).translate x (owner f h (0,0))) :=
  (stepSystem f h hc).axialAction.orbit_injective (owner f h (0,0)) (fiber f h)
    (rawAddress f h hc) 8 (fun a => (fiber_length_bounds f h a).2)
    (rawAddress_cover f h hc) (rawAddress_bound f h hc)

/-- Reflection restores the original alphabet, whose macro-label order is
opposite to the author native child boundary order. -/
noncomputable def anchorAt (x : Position) : Anchor f :=
  (stepSystem f h hc).translate (reflectPosition x) (owner f h (0,0))

noncomputable def coordinate (a : Anchor f) : Position := reflectPosition (rawAddress f h hc a.val)

theorem anchorAt_coordinate (a : Anchor f) : anchorAt f h hc (coordinate f h hc a) = a := by
  unfold anchorAt coordinate
  rw [reflectPosition_involutive,← rawAddress_spec,owner_self]

theorem anchorAt_injective : Function.Injective (anchorAt f h hc) := by
  intro x y he
  have hh := raw_orbit_injective f h hc he
  have hi := congrArg reflectPosition hh
  simpa only [reflectPosition_involutive] using hi

theorem coordinate_anchorAt (x : Position) : coordinate f h hc (anchorAt f h hc x) = x :=
  anchorAt_injective f h hc (anchorAt_coordinate f h hc _)

theorem anchorAt_direction (x : Position) (d : Fin 6) :
    anchorAt f h hc (addPos x (direction d)) =
      neighbor f h (inverseTurn d) (anchorAt f h hc x) := by
  unfold anchorAt
  rw [reflectPosition_add,reflectPosition_direction]
  have he : addPos (reflectPosition x) (direction (inverseTurn d)) =
      addPos (direction (inverseTurn d)) (reflectPosition x) := by
    apply Prod.ext <;> simp only [addPos] <;> omega
  rw [he,HexStepSystem.translate_add,HexStepSystem.translate_direction]
  rfl

noncomputable def coarseField (x : Position) : State := coarseState f h (anchorAt f h hc x)

theorem coarseField_globallyLegal : GloballyLegal (coarseField f h hc) := by
  intro x y hxy
  change x ≠ y ∧ _
  refine ⟨hxy,?_⟩
  intro d hd
  change y = addPos x (direction d) at hd
  subst y
  have hm := neighbor_reflected_marks f h hc d (anchorAt f h hc x)
  change facingMark (placed (x,coarseState f h (anchorAt f h hc x))) d =
    -facingMark (placed (addPos x (direction d),coarseState f h (anchorAt f h hc (addPos x (direction d))))) (opposite d)
  rw [anchorAt_direction]
  exact hm

end SpectreFinite.HexSearch.NativeCoarse
