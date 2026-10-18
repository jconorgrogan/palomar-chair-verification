module

public import SpectreFinite.RadiusThreeFastChecking

@[expose] public section


/-! Exact full-domain shortcuts for the subset and unscoped-preservation
part of the original replacement checker. None still denotes all 54 states. -/
namespace SpectreFinite.HexSearch.HigherFastChecking
open SpectreFinite.FiniteTable

def fastSubset (larger smaller : Option (List State)) : Bool :=
  match larger with
  | none => true
  | some values => (smaller.getD stateChoices).all (fun s => decide (s ∈ values))

theorem fastSubset_eq (larger smaller : Option (List State)) :
    fastSubset larger smaller =
      (smaller.getD stateChoices).all (fun s => decide (s ∈ larger.getD stateChoices)) := by
  cases larger with
  | none =>
    change true = (smaller.getD stateChoices).all (fun s => decide (s ∈ stateChoices))
    symm
    apply List.all_eq_true.mpr
    intro s _
    simp only [mem_stateChoices, decide_true]
  | some values => rfl

def checkReplacementRestFast {n : Nat} (scope : List (Fin n))
    (current proposed : FastDomains n) : Bool :=
  (List.finRange n).all (fun v =>
    fastSubset (current v) (proposed v) &&
      if v ∈ scope then true else fastSubset (proposed v) (current v))

theorem checkReplacementRestFast_eq {n : Nat} (scope : List (Fin n))
    (current proposed : FastDomains n) :
    checkReplacementRestFast scope current proposed =
      (List.finRange n).all (fun v =>
        (expandDomains proposed v).all (fun s => decide (s ∈ expandDomains current v)) &&
        if v ∈ scope then true else
          (expandDomains current v).all (fun s => decide (s ∈ expandDomains proposed v))) := by
  simp only [checkReplacementRestFast, fastSubset_eq, expandDomains]
  rfl

theorem checkReplacement_of_fast_rest {n : Nat} (c : Constraint n State)
    (current proposed : Domains n State) (fastCurrent fastProposed : FastDomains n)
    (hcurrent : current = expandDomains fastCurrent)
    (hproposed : proposed = expandDomains fastProposed)
    (hnarrowing : checkNarrowing c current proposed = true)
    (hrest : checkReplacementRestFast c.scope fastCurrent fastProposed = true) :
    checkReplacement c current proposed = true := by
  unfold checkReplacement
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact hnarrowing
  · rw [hcurrent, hproposed, ← checkReplacementRestFast_eq]
    exact hrest

#print axioms fastSubset_eq
#print axioms checkReplacement_of_fast_rest
end SpectreFinite.HexSearch.HigherFastChecking
