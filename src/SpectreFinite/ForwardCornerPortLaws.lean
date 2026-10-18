module

public import SpectreFinite.ForwardPortActions

@[expose] public section


/-! Consecutive exposed sides at one native child corner occur either
consecutively inside one macro-seam, or across its next macro-marker. -/
namespace SpectreFinite.HexSearch.ForwardSubstitution
open Boundary

def ExternalCornerLaw (k : TileKind) : PortAction → PortAction → Prop
  | .external s n, .external t m =>
    (s = t ∧ m.val = n.val + 1) ∨
    (t = rotateTurn 1 s ∧ n.val + 1 = (segment k s).length ∧ m = 0)
  | _, _ => True
instance (k : TileKind) (a b : PortAction) : Decidable (ExternalCornerLaw k a b) := by
  cases a <;> cases b <;> dsimp [ExternalCornerLaw] <;> infer_instance

def CornerPortLaws (k : TileKind) : Prop :=
  ∀ i : Fin 8, i.val < (children k).length → ∀ d : Fin 6,
    ExternalCornerLaw k (portAction k i d) (portAction k i (rotateTurn 1 d))
instance (k : TileKind) : Decidable (CornerPortLaws k) :=
  inferInstanceAs (Decidable (∀ i : Fin 8, _ → ∀ d : Fin 6, _))

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private theorem corner_port_laws_0 : CornerPortLaws 0 := by decide
private theorem corner_port_laws_1 : CornerPortLaws 1 := by decide
private theorem corner_port_laws_2 : CornerPortLaws 2 := by decide
private theorem corner_port_laws_3 : CornerPortLaws 3 := by decide
private theorem corner_port_laws_4 : CornerPortLaws 4 := by decide
private theorem corner_port_laws_5 : CornerPortLaws 5 := by decide
private theorem corner_port_laws_6 : CornerPortLaws 6 := by decide
private theorem corner_port_laws_7 : CornerPortLaws 7 := by decide
private theorem corner_port_laws_8 : CornerPortLaws 8 := by decide

theorem all_corner_port_laws : ∀ k : TileKind, CornerPortLaws k :=
  (Fin.cases corner_port_laws_0 (Fin.cases corner_port_laws_1 (Fin.cases corner_port_laws_2 (Fin.cases corner_port_laws_3 (Fin.cases corner_port_laws_4 (Fin.cases corner_port_laws_5 (Fin.cases corner_port_laws_6 (Fin.cases corner_port_laws_7 (Fin.cases corner_port_laws_8 (fun i => Fin.elim0 i))))))))))

theorem external_corner_order (k : TileKind) (i : Fin 8) (d s t n m : Fin 6)
    (hi : i.val < (children k).length)
    (h : portAction k i d = .external s n)
    (h' : portAction k i (rotateTurn 1 d) = .external t m) :
    (s = t ∧ m.val = n.val + 1) ∨
    (t = rotateTurn 1 s ∧ n.val + 1 = (segment k s).length ∧ m = 0) := by
  have hc := all_corner_port_laws k i hi d
  simpa only [h, h', ExternalCornerLaw] using hc

theorem external_corner_same_or_next (k : TileKind) (i : Fin 8) (d s t n m : Fin 6)
    (hi : i.val < (children k).length)
    (h : portAction k i d = .external s n)
    (h' : portAction k i (rotateTurn 1 d) = .external t m) :
    s = t ∨ t = rotateTurn 1 s := by
  rcases external_corner_order k i d s t n m hi h h' with hs | ht
  · exact Or.inl hs.1
  · exact Or.inr ht.1

end SpectreFinite.HexSearch.ForwardSubstitution
