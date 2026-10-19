module
public import Fixture
@[expose] public section
namespace DomainAliasFixture
def originalFast (v : Fin 2) : Option (List Nat) :=
  match v.val with
  | 0 => some [0]
  | _ => some [1]
theorem original_fast_equals_actual : originalFast = Fast := by
  funext v
  exact (show ∀ v : Fin 2, originalFast v = Fast v from by decide) v
end DomainAliasFixture
