module

public import SpectreFinite.FiniteTableCover
public import SpectreFinite.HexSearchModel

@[expose] public section


/-! A proved evaluation shortcut for the full 54-state domain. None means
exactly stateChoices, not an omitted variable or an unchecked assumption. -/
namespace SpectreFinite.HexSearch.HigherFastChecking
open SpectreFinite.FiniteTable

abbrev FastDomains (n : Nat) := Fin n → Option (List State)
def expandDomains {n : Nat} (domains : FastDomains n) : Domains n State :=
  fun v => (domains v).getD stateChoices

def rowCompatibleFast {n : Nat} (domains : FastDomains n) :
    List (Fin n) → List State → Bool
  | [], [] => true
  | v :: vs, s :: ss =>
    (match domains v with
    | none => true
    | some choices => decide (s ∈ choices)) && rowCompatibleFast domains vs ss
  | _, _ => false

theorem rowCompatibleFast_eq {n : Nat} (domains : FastDomains n)
    (scope : List (Fin n)) (row : List State) :
    rowCompatibleFast domains scope row = rowCompatible (expandDomains domains) scope row := by
  induction scope generalizing row with
  | nil => cases row <;> rfl
  | cons v vs ih =>
    cases row with
    | nil => rfl
    | cons s ss =>
      cases h : domains v with
      | none => simp [rowCompatibleFast, rowCompatible, expandDomains, h, mem_stateChoices, ih]
      | some choices => simp [rowCompatibleFast, rowCompatible, expandDomains, h, ih]

def checkNarrowingFast {n : Nat} (c : Constraint n State)
    (current proposed : FastDomains n) : Bool :=
  c.rows.all (fun row => if rowCompatibleFast current c.scope row then
    rowCompatibleFast proposed c.scope row else true)

theorem checkNarrowingFast_eq {n : Nat} (c : Constraint n State)
    (current proposed : FastDomains n) :
    checkNarrowingFast c current proposed =
      checkNarrowing c (expandDomains current) (expandDomains proposed) := by
  simp only [checkNarrowingFast, checkNarrowing, rowCompatibleFast_eq]

theorem checkNarrowing_of_fast {n : Nat} (c : Constraint n State)
    (current proposed : Domains n State) (fastCurrent fastProposed : FastDomains n)
    (hcurrent : current = expandDomains fastCurrent)
    (hproposed : proposed = expandDomains fastProposed)
    (hcheck : checkNarrowingFast c fastCurrent fastProposed = true) :
    checkNarrowing c current proposed = true := by
  rw [hcurrent, hproposed, ← checkNarrowingFast_eq]
  exact hcheck

#print axioms rowCompatibleFast_eq
#print axioms checkNarrowing_of_fast
end SpectreFinite.HexSearch.HigherFastChecking
