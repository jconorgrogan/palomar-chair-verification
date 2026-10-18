module

public import SpectreFinite.ParentBoundaryNeighborLaws
public import SpectreFinite.ReflectedMacroLabels

@[expose] public section


/-! Actual neighboring parent marks complement. The reflection needed to
reuse the original marked-hexagon alphabet is applied explicitly. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership Boundary NativeCoarse

theorem neighbor_macro_complement_of_frame (f : Position → State) (h : Recognition f)
    (a : Anchor f) (k : TileKind) (ns : List Position) (frames : List FrameInfo)
    (hp : rootParent (normalizedAt f a.val) = childPatch k)
    (hb : Structure (owners (normalizedAt f a.val)) k ns)
    (hg : FrameGeometry k ns frames) (hr : FrameRows (normalizedAt f a.val) frames)
    (s : Fin 6) :
    macroLabel (parentKind f h a) s =
      -macroLabel (parentKind f h (neighbor f h (rotateTurn (f a.val).2 s) a))
        (rotateTurn (inverseTurn (f (neighbor f h (rotateTurn (f a.val).2 s) a).val).2)
          (opposite (rotateTurn (f a.val).2 s))) := by
  have hk := parentKind_unique f h a k
    (exactParentAt_of_rootParent f a.val a.property k hp)
  have hd : rotateTurn (f (neighbor f h (rotateTurn (f a.val).2 s) a).val).2
      (frameAt frames s).mateSide = opposite (rotateTurn (f a.val).2 s) := by
    rw [neighbor_turn_local f h a k ns frames hp hb hg hr, ← rotateTurn_assoc]
    rw [show rotateTurn (frameAt frames s).turn (frameAt frames s).mateSide = opposite s
      from (hg.2.2.2.1 s).2.2]
    exact rotateTurn_opposite (f a.val).2 s
  rw [← hd, rotateTurn_inverse, ← hk,
    neighbor_kind_of_frame f h a k ns frames hp hb hg hr,rotateTurn_inverse]
  exact (hg.2.2.2.1 s).2.1

theorem neighbor_macro_complement (f : Position → State) (h : Recognition f)
    (hc : ∀ a : Anchor f, FramedRootStructure (normalizedAt f a.val))
    (d : Fin 6) (a : Anchor f) :
    macroLabel (parentKind f h a) (rotateTurn (inverseTurn (f a.val).2) d) =
      -macroLabel (parentKind f h (neighbor f h d a))
        (rotateTurn (inverseTurn (f (neighbor f h d a).val).2) (opposite d)) := by
  obtain ⟨k,ns,frames,hp,hb,hg,hr⟩ := hc a
  have hm := neighbor_macro_complement_of_frame f h a k ns frames hp hb hg hr
    (rotateTurn (inverseTurn (f a.val).2) d)
  simpa only [rotateTurn_inverse_right] using hm

/-- In the original marked alphabet, reflect direction d to -d and use
coarse state (actual kind, minus actual Gamma turn). -/
theorem neighbor_reflected_marks (f : Position → State) (h : Recognition f)
    (hc : ∀ a : Anchor f, FramedRootStructure (normalizedAt f a.val))
    (d : Fin 6) (a : Anchor f) :
    facingMark (placed ((0,0),coarseState f h a)) d =
      -facingMark (placed ((0,0),coarseState f h (neighbor f h (inverseTurn d) a)))
        (opposite d) := by
  apply reflected_macro_matching
  have hm := neighbor_macro_complement f h hc (inverseTurn d) a
  simpa only [inverseTurn_opposite] using hm

#print axioms neighbor_macro_complement_of_frame
#print axioms neighbor_macro_complement
#print axioms neighbor_reflected_marks
end SpectreFinite.HexSearch.ParentBoundary
