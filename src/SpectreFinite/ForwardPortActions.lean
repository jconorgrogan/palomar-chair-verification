module

public import SpectreFinite.ForwardSeamGeometry
public import SpectreFinite.BoundaryGrowth

@[expose] public section


/-! Explicit finite port routing in one literal supertile. The search tables
are definitions from the listed children and complete macro-segment lists. -/
namespace SpectreFinite.HexSearch.ForwardSubstitution
open Boundary

inductive PortAction where
  | internal (child : Fin 8)
  | external (side : Fin 6) (index : Fin 6)
  deriving DecidableEq

def childAt (k : TileKind) (i : Fin 8) : PlacedHex :=
  (children k).getD i.val defaultHex

def segmentSlots : List (Fin 6 × Fin 6) :=
  (List.finRange 6).flatMap fun s => (List.finRange 6).map fun n => (s,n)

/-- Internal adjacency takes precedence. Every remaining in-bounds side has
exactly one macro-side/segment-index address; this is checked below. -/
def portAction (k : TileKind) (i : Fin 8) (d : Fin 6) : PortAction :=
  match (List.finRange 8).find? (fun j => decide (j.val < (children k).length ∧
      pos (childAt k j) = addPos (pos (childAt k i)) (direction d))) with
  | some j => .internal j
  | none =>
      let sn := (segmentSlots.find? fun sn =>
        decide ((segment k sn.1)[sn.2.val]? = some ⟨i.val,d⟩)).getD (0,0)
      .external sn.1 sn.2

/-- The literal child and local side at the reversed segment index. -/
def matingPort (k : TileKind) (s n : Fin 6) : Fin 8 × Fin 6 :=
  let e := (segment k s).reverse.getD n.val ⟨0,0⟩
  (⟨e.child % 8, Nat.mod_lt _ (by decide)⟩, e.side)

def ValidPortAction (k : TileKind) (i : Fin 8) (d : Fin 6) : PortAction → Prop
  | .internal j => j.val < (children k).length ∧
      pos (childAt k j) = addPos (pos (childAt k i)) (direction d)
  | .external s n => (segment k s)[n.val]? = some ⟨i.val,d⟩
instance (k : TileKind) (i : Fin 8) (d : Fin 6) (a : PortAction) :
    Decidable (ValidPortAction k i d a) := by
  cases a <;> unfold ValidPortAction <;> infer_instance

def PortActionCertificate (k : TileKind) : Prop :=
  (∀ i : Fin 8, i.val < (children k).length → ∀ d : Fin 6,
    ValidPortAction k i d (portAction k i d)) ∧
  (∀ s n : Fin 6, ∀ i : Fin 8, ∀ d : Fin 6,
    (segment k s)[n.val]? = some ⟨i.val,d⟩ →
    i.val < (children k).length ∧ portAction k i d = .external s n) ∧
  (∀ s n : Fin 6, n.val < (segment k s).length →
    (matingPort k s n).1.val < (children k).length)
instance (k : TileKind) : Decidable (PortActionCertificate k) :=
  inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private theorem port_actions_0 : PortActionCertificate 0 := by decide
private theorem port_actions_1 : PortActionCertificate 1 := by decide
private theorem port_actions_2 : PortActionCertificate 2 := by decide
private theorem port_actions_3 : PortActionCertificate 3 := by decide
private theorem port_actions_4 : PortActionCertificate 4 := by decide
private theorem port_actions_5 : PortActionCertificate 5 := by decide
private theorem port_actions_6 : PortActionCertificate 6 := by decide
private theorem port_actions_7 : PortActionCertificate 7 := by decide
private theorem port_actions_8 : PortActionCertificate 8 := by decide

theorem all_port_actions : ∀ k : TileKind, PortActionCertificate k :=
  Fin.cases port_actions_0 (Fin.cases port_actions_1 (Fin.cases port_actions_2
    (Fin.cases port_actions_3 (Fin.cases port_actions_4 (Fin.cases port_actions_5
    (Fin.cases port_actions_6 (Fin.cases port_actions_7 (Fin.cases port_actions_8
      (fun i => Fin.elim0 i)))))))))

end SpectreFinite.HexSearch.ForwardSubstitution
