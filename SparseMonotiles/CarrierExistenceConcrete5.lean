module

public import SparseMonotiles.CarrierExistenceLegality
public import SparseMonotiles.CoarseContactCertificates5Base

@[expose] public section

/-! T5-only constructed world, so existence does not depend on seven-dimensional
static certificate replay. The substitution is the exact Catalog5 child rule. -/
namespace SparseMonotiles.CarrierHierarchy.Existence.Catalog5World
open Contact

theorem empty_child : Catalog5.childPerm (fun _ => false) = Equiv.refl _ := by decide

def registered : RegisteredWorld 5 := Existence.world (by decide) Catalog5.childPerm empty_child

theorem legal (rules : ForwardRules CoarseContactCertificates5.C M5) : registered.Legal M5 :=
  world_legal (by decide) Catalog5.childPerm empty_child
    CoarseContactCertificates5.C M5 CoarseContactCertificates5.child_table_covers rules

#print axioms registered
#print axioms legal
end SparseMonotiles.CarrierHierarchy.Existence.Catalog5World
