module

public import SpectreClusters.ReverseClusterCocyclePair0
public import SpectreClusters.ReverseClusterCocyclePair1
public import SpectreClusters.ReverseClusterCocyclePair2
public import SpectreClusters.ReverseClusterCocyclePair3
public import SpectreClusters.ReverseClusterCocyclePair4
public import SpectreClusters.ReverseClusterCocyclePair5
public import SpectreClusters.ReverseClusterCocyclePair6
public import SpectreClusters.ReverseClusterCocyclePair7
public import SpectreClusters.ReverseClusterCocyclePair8
public import SpectreClusters.ReverseClusterCocycleIntegration

@[expose] public section


namespace SpectreClusters.ReverseExistence
open SpectreFinite SpectreFinite.HexSearch

theorem all_pair_certificates : ∀ k : Fin 9, PairCertificate k :=
  Fin.cases pair_certificate_0 (Fin.cases pair_certificate_1 (Fin.cases pair_certificate_2 (Fin.cases pair_certificate_3 (Fin.cases pair_certificate_4 (Fin.cases pair_certificate_5 (Fin.cases pair_certificate_6 (Fin.cases pair_certificate_7 (Fin.cases pair_certificate_8 (fun i => Fin.elim0 i)))))))))

theorem vertexDelta_end (a b : State) (d : Fin 6) (h : sideMatch a b d) :
    vertexDelta a b d = sub (stateCorner a (rotateTurn 1 d)) (stateCorner b (opposite d)) :=
  (all_pair_certificates a.1 a.2 b.1 b.2 d h).1

theorem centerDelta_lattice (a b : State) (d : Fin 6) (h : sideMatch a b d) :
    lattice (centerDelta a b d) = vertexDelta a b d :=
  (all_pair_certificates a.1 a.2 b.1 b.2 d h).2

theorem sideMatch_swap (a b : State) (d : Fin 6) (h : sideMatch a b d) :
    sideMatch b a (opposite d) := by
  unfold sideMatch at *
  rw [opposite_involutive]
  omega

private theorem turn_four_opposite : ∀ d : Fin 6,
    rotateTurn 4 (opposite d) = rotateTurn 1 d := by decide
private theorem turn_one_two : ∀ d : Fin 6,
    rotateTurn 1 (rotateTurn 2 d) = opposite d := by decide
private theorem opposite_two : ∀ d : Fin 6,
    opposite (rotateTurn 2 d) = rotateTurn 4 (rotateTurn 1 d) := by decide

theorem vertexDelta_inverse (a b : State) (d : Fin 6) (h : sideMatch a b d) :
    add (vertexDelta a b d) (vertexDelta b a (opposite d)) = (0,0) := by
  rw [vertexDelta_end a b d h]
  unfold vertexDelta
  rw [turn_four_opposite]
  apply Prod.ext <;> simp [add,sub] <;> omega

theorem vertexDelta_triangle (a b c : State) (d : Fin 6)
    (hab : sideMatch a b d) (hbc : sideMatch b c (rotateTurn 2 d)) :
    add (vertexDelta a b d) (vertexDelta b c (rotateTurn 2 d)) =
      vertexDelta a c (rotateTurn 1 d) := by
  rw [vertexDelta_end a b d hab,vertexDelta_end b c (rotateTurn 2 d) hbc]
  unfold vertexDelta
  rw [turn_one_two,opposite_two]
  apply Prod.ext <;> simp [add,sub] <;> omega

theorem centerDelta_inverse (a b : State) (d : Fin 6) (h : sideMatch a b d) :
    add (centerDelta a b d) (centerDelta b a (opposite d)) = (0,0) := by
  apply lattice_injective
  rw [lattice_add,centerDelta_lattice a b d h,
    centerDelta_lattice b a (opposite d) (sideMatch_swap a b d h)]
  exact vertexDelta_inverse a b d h

theorem centerDelta_triangle (a b c : State) (d : Fin 6)
    (hab : sideMatch a b d) (hac : sideMatch a c (rotateTurn 1 d))
    (hbc : sideMatch b c (rotateTurn 2 d)) :
    add (centerDelta a b d) (centerDelta b c (rotateTurn 2 d)) =
      centerDelta a c (rotateTurn 1 d) := by
  apply lattice_injective
  rw [lattice_add,centerDelta_lattice a b d hab,
    centerDelta_lattice b c (rotateTurn 2 d) hbc,
    centerDelta_lattice a c (rotateTurn 1 d) hac]
  exact vertexDelta_triangle a b c d hab hbc

private theorem direction_nonzero : ∀ d : Fin 6, direction d ≠ (0,0) := by decide

theorem field_sideMatch (f : Position → State) (hf : GloballyLegal f)
    (x : Position) (d : Fin 6) : sideMatch (f x) (f (addPos x (direction d))) d := by
  have hne : x ≠ addPos x (direction d) := by
    intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    have hz : direction d = (0,0) := by
      apply Prod.ext <;> simp [addPos] at * <;> omega
    exact direction_nonzero d hz
  exact (hf x (addPos x (direction d)) hne).2 d rfl

def fieldDelta (f : Position → State) (x : Position) (d : Fin 6) : Point :=
  centerDelta (f x) (f (addPos x (direction d))) d

theorem fieldDelta_closed (f : Position → State) (hf : GloballyLegal f) :
    ClosedCocycle (fieldDelta f) := by
  constructor
  · intro x d
    have he : addPos (addPos x (direction d)) (direction (opposite d)) = x := by
      rw [direction_opposite]
      apply Prod.ext <;> simp [addPos] <;> omega
    unfold fieldDelta
    rw [he]
    exact centerDelta_inverse _ _ d (field_sideMatch f hf x d)
  · intro x d
    have hdir : addPos (direction d) (direction (rotateTurn 2 d)) =
        direction (rotateTurn 1 d) := by
      exact (by decide : ∀ t : Fin 6, addPos (direction t) (direction (rotateTurn 2 t)) =
        direction (rotateTurn 1 t)) d
    have he : addPos (addPos x (direction d)) (direction (rotateTurn 2 d)) =
        addPos x (direction (rotateTurn 1 d)) := by
      have hx := congrArg Prod.fst hdir
      have hy := congrArg Prod.snd hdir
      apply Prod.ext <;> simp [addPos] at * <;> omega
    have hbc := field_sideMatch f hf (addPos x (direction d)) (rotateTurn 2 d)
    rw [he] at hbc
    unfold fieldDelta
    rw [he]
    exact centerDelta_triangle _ _ _ d (field_sideMatch f hf x d)
      (field_sideMatch f hf x (rotateTurn 1 d)) hbc

/-- An actual globally legal marked field now has consistent integer cluster
anchors. Global no-overlap and coverage are not claimed by this theorem. -/
def developedAnchor (f : Position → State) (hf : GloballyLegal f) : Position → Point :=
  integratedAnchor (fieldDelta f) (fieldDelta_closed f hf)

theorem developedAnchor_zero (f : Position → State) (hf : GloballyLegal f) :
    developedAnchor f hf (0,0) = (0,0) := rfl

theorem developedAnchor_step (f : Position → State) (hf : GloballyLegal f)
    (x : Position) (d : Fin 6) :
    developedAnchor f hf (addPos x (direction d)) =
      add (developedAnchor f hf x) (centerDelta (f x) (f (addPos x (direction d))) d) :=
  integratedAnchor_step (fieldDelta f) (fieldDelta_closed f hf) x d

end SpectreClusters.ReverseExistence
