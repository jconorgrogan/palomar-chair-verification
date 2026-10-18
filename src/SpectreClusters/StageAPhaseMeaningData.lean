module

public import SpectreClusters.StageAPhaseModel
public import SpectreClusters.StageALocalClaims

@[expose] public section


namespace SpectreClusters.StageA

def specialRowB : HTKind → Nat → Bool
  | .hat, i => i == 210
  | .turtle, i => i == 0

def allOppositeRowB (kind : HTKind) (i : Nat) : Bool :=
  (neighbors kind i).all fun p => !(p.kind == kind)

set_option maxRecDepth 100000 in
theorem allOppositeRow_special_check (kind : HTKind) :
    (keptIds 2 kind).all (fun i => allOppositeRowB kind i == specialRowB kind i) = true := by
  cases kind <;> rfl

theorem allOppositeRow_eq_special (kind : HTKind) (i : Nat) (hi : i ∈ keptIds 2 kind) :
    allOppositeRowB kind i = specialRowB kind i := by
  have h := List.all_eq_true.mp (allOppositeRow_special_check kind) i hi
  simpa using h

end SpectreClusters.StageA
