module

public import SpectreFinite.ForwardPortActions

@[expose] public section


/-! Direct port-level triangle predicates for literal two- and three-parent
substitution neighborhoods. No geometric embedding or input field is used. -/
namespace SpectreFinite.HexSearch.ForwardSubstitution
open Boundary

/-- A fine direction written in the root frame, transported to its neighbor. -/
def seamLocal (s t d : Fin 6) : Fin 6 :=
  rotateTurn (inverseTurn (seamTurn s t)) d

def PairPortTriangleConclusion (k l : TileKind) (s t d : Fin 6) :
    PortAction → PortAction → Prop
  | .internal j, .internal _ => True
  | .internal j, .external a n => a = s → ∃ m : Fin 6,
      portAction k j (rotateTurn 2 d) = .external s m ∧
      (matingPort l t m).1 = (matingPort l t n).1
  | .external a n, .internal j => a = s → ∃ m : Fin 6,
      portAction l (matingPort l t n).1 (seamLocal s t (rotateTurn 2 d)) = .external t m ∧
      (matingPort k s m).1 = j
  | .external a n, .external b m => a = s → b = s →
      portAction l (matingPort l t n).1 (seamLocal s t (rotateTurn 2 d)) =
        .internal (matingPort l t m).1
instance (k l : TileKind) (s t d : Fin 6) (a b : PortAction) :
    Decidable (PairPortTriangleConclusion k l s t d a b) := by
  cases a <;> cases b <;> unfold PairPortTriangleConclusion <;> infer_instance

def PairPortTriangles (k l : TileKind) (s t : Fin 6) : Prop :=
  ∀ i : Fin 8, i.val < (children k).length → ∀ d : Fin 6,
    PairPortTriangleConclusion k l s t d
      (portAction k i d) (portAction k i (rotateTurn 1 d))
instance (k l : TileKind) (s t : Fin 6) : Decidable (PairPortTriangles k l s t) :=
  inferInstanceAs (Decidable (∀ i : Fin 8, i.val < (children k).length → ∀ d : Fin 6,
    PairPortTriangleConclusion k l s t d
      (portAction k i d) (portAction k i (rotateTurn 1 d))))

def PairPortTriangleCertificate (k l : TileKind) (s t : Fin 6) : Prop :=
  macroLabel k s = -macroLabel l t → PairPortTriangles k l s t
instance (k l : TileKind) (s t : Fin 6) :
    Decidable (PairPortTriangleCertificate k l s t) :=
  inferInstanceAs (Decidable (macroLabel k s = -macroLabel l t → PairPortTriangles k l s t))

def TriplePortTriangleConclusion (k l m : TileKind) (s t u d : Fin 6) :
    PortAction → PortAction → Prop
  | .external a n, .external b h => a = s → b = rotateTurn 1 s → ∃ j : Fin 6,
      portAction l (matingPort l t n).1 (seamLocal s t (rotateTurn 2 d)) =
        .external (rotateTurn 5 t) j ∧
      (matingPort m (rotateTurn 1 u) j).1 = (matingPort m u h).1
  | _, _ => True
instance (k l m : TileKind) (s t u d : Fin 6) (a b : PortAction) :
    Decidable (TriplePortTriangleConclusion k l m s t u d a b) := by
  cases a <;> cases b <;> unfold TriplePortTriangleConclusion <;> infer_instance

def TriplePortTriangles (k l m : TileKind) (s t u : Fin 6) : Prop :=
  ∀ i : Fin 8, i.val < (children k).length → ∀ d : Fin 6,
    TriplePortTriangleConclusion k l m s t u d
      (portAction k i d) (portAction k i (rotateTurn 1 d))
instance (k l m : TileKind) (s t u : Fin 6) : Decidable (TriplePortTriangles k l m s t u) :=
  inferInstanceAs (Decidable (∀ i : Fin 8, i.val < (children k).length → ∀ d : Fin 6,
    TriplePortTriangleConclusion k l m s t u d
      (portAction k i d) (portAction k i (rotateTurn 1 d))))

/-- The root has consecutive native macro-sides s and s+1. -/
def RootPortTriangleCertificate (k : TileKind) (s : Fin 6) : Prop :=
  ∀ l : TileKind, ∀ t : Fin 6,
    macroLabel k s = -macroLabel l t →
    ∀ m : TileKind, ∀ u : Fin 6,
      macroLabel k (rotateTurn 1 s) = -macroLabel m u →
      macroLabel l (rotateTurn 5 t) = -macroLabel m (rotateTurn 1 u) →
      TriplePortTriangles k l m s t u

end SpectreFinite.HexSearch.ForwardSubstitution
