module

public import SpectreFinite.ForwardPortActions

@[expose] public section


/-! Exact algebra of literal reversed seam indices and child ports. These
certificates quantify over every complementary macro pair, without a field. -/
namespace SpectreFinite.HexSearch.ForwardSubstitution
open Boundary

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def forwardPort (k : TileKind) (s n : Fin 6) : Fin 8 × Fin 6 :=
  let e := (segment k s).getD n.val ⟨0,0⟩
  (⟨e.child % 8, Nat.mod_lt _ (by decide)⟩, e.side)

def reverseSlot (k : TileKind) (s n : Fin 6) : Fin 6 :=
  ⟨((segment k s).length - 1 - n.val) % 6, Nat.mod_lt _ (by decide)⟩

def SeamPortLaw (k l : TileKind) (s t : Fin 6) : Prop :=
  (segment k s).length = (segment l t).length ∧
  ∀ n : Fin 6, n.val < (segment k s).length →
    let e := forwardPort k s n
    let f := matingPort l t n
    let m := reverseSlot k s n
    e.1.val < (children k).length ∧ f.1.val < (children l).length ∧
    portAction k e.1 e.2 = .external s n ∧
    portAction l f.1 f.2 = .external t m ∧
    matingPort k s m = e ∧
    rotateTurn (seamTurn s t) f.2 = opposite e.2 ∧
    facingMark (childAt k e.1) e.2 = -facingMark (childAt l f.1) f.2
instance (k l : TileKind) (s t : Fin 6) : Decidable (SeamPortLaw k l s t) :=
  inferInstanceAs (Decidable (_ ∧ _))

def KindSeamPortLaws (k : TileKind) : Prop :=
  ∀ l : TileKind, ∀ s t : Fin 6,
    macroLabel k s = -macroLabel l t → SeamPortLaw k l s t
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
end SpectreFinite.HexSearch.ForwardSubstitution
