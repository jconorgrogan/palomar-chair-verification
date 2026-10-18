module

public import SpectreClusters.StageAT7OverlapData

@[expose] public section


/-! Complete relative-pose enumeration from equality of a shared literal
T7H tile. No bounded coordinate premise or guessed search region is used. -/
namespace SpectreClusters.StageA

def alignTurtle (a b : HTPlacement) : HTPlacement :=
  ⟨.turtle,turnDiff a.turn b.turn,sub a.center (rotate (turnDiff a.turn b.turn) b.center)⟩

theorem alignTurtle_moved (root p : HTPlacement) (hk : root.kind = .turtle) :
    alignTurtle (movePlacement root.turn root.center p) p = root := by
  cases root with
  | mk kind turn center =>
    cases hk
    simp [alignTurtle,movePlacement,turnDiff_add,sub,add]

set_option maxRecDepth 100000 in
theorem t7SharedAlignment_check :
    (clusterPieces .t7h).all (fun a => (clusterPieces .t7h).all (fun b =>
      !(a.kind == b.kind) || poseEqB (alignTurtle a b) (canonicalRoot .turtle) ||
        t7SharedOtherRoots.contains (alignTurtle a b))) = true := by rfl

theorem t7SharedAlignment_complete (a b : HTPlacement)
    (ha : a ∈ clusterPieces .t7h) (hb : b ∈ clusterPieces .t7h)
    (hk : a.kind = b.kind) :
    alignTurtle a b = canonicalRoot .turtle ∨ alignTurtle a b ∈ t7SharedOtherRoots := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp t7SharedAlignment_check a ha) b hb
  simpa [hk,poseEqB_iff] using h

end SpectreClusters.StageA
