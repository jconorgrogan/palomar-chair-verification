module

public import SpectreFinite.ForwardPortActions

@[expose] public section


/-! The explicit internal routing algorithm satisfies inverse, matching,
and triangle laws, independently of any surrounding parent field. -/
namespace SpectreFinite.HexSearch.ForwardSubstitution

def InternalInverseLaw (k : TileKind) (i : Fin 8) (d : Fin 6) : PortAction → Prop
  | .internal j =>
    portAction k j (opposite d) = .internal i ∧
    facingMark (childAt k i) d = -facingMark (childAt k j) (opposite d)
  | .external _ _ => True
instance (k : TileKind) (i : Fin 8) (d : Fin 6) (a : PortAction) :
    Decidable (InternalInverseLaw k i d a) := by
  cases a <;> dsimp [InternalInverseLaw] <;> infer_instance

def InternalTriangleLaw (k : TileKind) (d : Fin 6) : PortAction → PortAction → Prop
  | .internal j, .internal h => portAction k j (rotateTurn 2 d) = .internal h
  | _, _ => True
instance (k : TileKind) (d : Fin 6) (a b : PortAction) :
    Decidable (InternalTriangleLaw k d a b) := by
  cases a <;> cases b <;> dsimp [InternalTriangleLaw] <;> infer_instance

def InternalPortLaws (k : TileKind) : Prop :=
  (∀ i : Fin 8, i.val < (children k).length → ∀ d : Fin 6,
    InternalInverseLaw k i d (portAction k i d)) ∧
  (∀ i : Fin 8, i.val < (children k).length → ∀ d : Fin 6,
    InternalTriangleLaw k d (portAction k i d) (portAction k i (rotateTurn 1 d)))
instance (k : TileKind) : Decidable (InternalPortLaws k) :=
  inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private theorem internal_port_laws_0 : InternalPortLaws 0 := by decide
private theorem internal_port_laws_1 : InternalPortLaws 1 := by decide
private theorem internal_port_laws_2 : InternalPortLaws 2 := by decide
private theorem internal_port_laws_3 : InternalPortLaws 3 := by decide
private theorem internal_port_laws_4 : InternalPortLaws 4 := by decide
private theorem internal_port_laws_5 : InternalPortLaws 5 := by decide
private theorem internal_port_laws_6 : InternalPortLaws 6 := by decide
private theorem internal_port_laws_7 : InternalPortLaws 7 := by decide
private theorem internal_port_laws_8 : InternalPortLaws 8 := by decide

theorem all_internal_port_laws : ∀ k : TileKind, InternalPortLaws k :=
  (Fin.cases internal_port_laws_0 (Fin.cases internal_port_laws_1 (Fin.cases internal_port_laws_2 (Fin.cases internal_port_laws_3 (Fin.cases internal_port_laws_4 (Fin.cases internal_port_laws_5 (Fin.cases internal_port_laws_6 (Fin.cases internal_port_laws_7 (Fin.cases internal_port_laws_8 (fun i => Fin.elim0 i))))))))))

theorem internal_port_inverse (k : TileKind) (i j : Fin 8) (d : Fin 6)
    (hi : i.val < (children k).length) (h : portAction k i d = .internal j) :
    portAction k j (opposite d) = .internal i ∧
    facingMark (childAt k i) d = -facingMark (childAt k j) (opposite d) := by
  have hl := (all_internal_port_laws k).1 i hi d
  simpa only [h, InternalInverseLaw] using hl

theorem internal_port_triangle (k : TileKind) (i j z : Fin 8) (d : Fin 6)
    (hi : i.val < (children k).length)
    (h : portAction k i d = .internal j)
    (h' : portAction k i (rotateTurn 1 d) = .internal z) :
    portAction k j (rotateTurn 2 d) = .internal z := by
  have hl := (all_internal_port_laws k).2 i hi d
  simpa only [h, h', InternalTriangleLaw] using hl

end SpectreFinite.HexSearch.ForwardSubstitution
