module
public import Init
@[expose] public section
namespace DomainAliasFixture
def Domains (v : Fin 2) : List Nat :=
  match v.val with
  | 0 => [0]
  | _ => [1]
def Fast (v : Fin 2) : Option (List Nat) :=
  match v.val with
  | 0 => some [0]
  | _ => some [1]
theorem fast_eq : Domains = (fun v => (Fast v).getD []) := by
  funext v
  exact (show ∀ v : Fin 2, Domains v = (Fast v).getD [] from by decide) v
end DomainAliasFixture
