module
public import Init
@[expose] public section
namespace DomainAliasFixture
def Domains (v : Fin 2) : List Nat :=
  match v.val with
  | 0 => [1]
  | _ => [1]
def Fast (v : Fin 2) : Option (List Nat) :=
  some (Domains v)
theorem fast_eq : Domains = (fun v => (Fast v).getD []) := by
  funext v
  rfl
end DomainAliasFixture
