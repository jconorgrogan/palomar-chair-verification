module

public import SpectreFinite.FiniteTableNarrowing

@[expose] public section


/-! Checked literal domain replacement for efficient generated traces.
Unlike chained intersections, each accepted step returns the supplied literal
domains directly. Every reduction is justified by a complete original-table
scan, while finite-variable checks enforce inclusion and unchanged unscoped
values. This module is generic and makes no Spectre-specific table claim. -/
namespace SpectreFinite.FiniteTable

universe u
variable {n : Nat} {State : Type u} [DecidableEq State]

/-- Validate all changed domains. Proposed values must come from the old
domain; outside this constraint's scope, all old values must also remain.
Inside its scope, the separate full-row check establishes preservation. -/
def checkReplacement (c : Constraint n State) (current proposed : Domains n State) : Bool :=
  checkNarrowing c current proposed && (List.finRange n).all (fun v =>
    (proposed v).all (fun s => decide (s ∈ current v)) &&
    if v ∈ c.scope then true else (current v).all (fun s => decide (s ∈ proposed v)))

theorem checkReplacement_subset (c : Constraint n State) (current proposed : Domains n State)
    (hcheck : checkReplacement c current proposed = true)
    (v : Fin n) (s : State) (hs : s ∈ proposed v) : s ∈ current v := by
  have hparts := Bool.and_eq_true_iff.mp hcheck
  have hv := List.all_eq_true.mp hparts.2 v (List.mem_finRange v)
  have hsub := (Bool.and_eq_true_iff.mp hv).1
  exact of_decide_eq_true (List.all_eq_true.mp hsub s hs)

theorem checkReplacement_preserves (c : Constraint n State) (current proposed : Domains n State)
    (f : Assignment n State) (hf : Fits current f) (hc : SatisfiesConstraint c f)
    (hcheck : checkReplacement c current proposed = true) : Fits proposed f := by
  have hparts := Bool.and_eq_true_iff.mp hcheck
  have hnarrow := applyNarrowing_preserves c current proposed f hf hc hparts.1
  intro v
  by_cases hv : v ∈ c.scope
  · have h := hnarrow v
    simp only [applyNarrowing, hv, ↓reduceIte, List.mem_filter, decide_eq_true_eq] at h
    exact h.2
  · have hall := List.all_eq_true.mp hparts.2 v (List.mem_finRange v)
    have hkeep := (Bool.and_eq_true_iff.mp hall).2
    simp only [hv, ↓reduceIte] at hkeep
    exact of_decide_eq_true (List.all_eq_true.mp hkeep (f v) (hf v))

theorem solution_checkReplacement (constraints : List (Constraint n State))
    (c : Constraint n State) (hc : c ∈ constraints)
    (current proposed : Domains n State) (f : Assignment n State)
    (hf : Solution current constraints f)
    (hcheck : checkReplacement c current proposed = true) :
    Solution proposed constraints f :=
  ⟨checkReplacement_preserves c current proposed f hf.1 (hf.2 c hc) hcheck, hf.2⟩

theorem unsatisfiable_of_checked_replacement (constraints : List (Constraint n State))
    (c : Constraint n State) (hc : c ∈ constraints) (current proposed : Domains n State)
    (hcheck : checkReplacement c current proposed = true)
    (hu : Unsatisfiable proposed constraints) : Unsatisfiable current constraints :=
  fun f hf => hu f (solution_checkReplacement constraints c hc current proposed f hf hcheck)

/-- Each trace item chooses an original constraint by index and supplies the
next literal domain function. An invalid index or invalid step rejects the
whole trace. There is no assumed equality with a solver-produced result. -/
def runReplacementTrace (constraints : List (Constraint n State)) :
    Domains n State → List (Nat × Domains n State) → Option (Domains n State)
  | current, [] => some current
  | current, (index, proposed) :: rest =>
    match constraints[index]? with
    | none => none
    | some c => if checkReplacement c current proposed then
        runReplacementTrace constraints proposed rest else none

theorem runReplacementTrace_preserves (constraints : List (Constraint n State))
    (current : Domains n State) (trace : List (Nat × Domains n State))
    (result : Domains n State) (hrun : runReplacementTrace constraints current trace = some result)
    (f : Assignment n State) (hf : Solution current constraints f) :
    Solution result constraints f := by
  induction trace generalizing current with
  | nil =>
    simp only [runReplacementTrace, Option.some.injEq] at hrun
    exact hrun ▸ hf
  | cons step rest ih =>
    rcases step with ⟨index, proposed⟩
    cases hc : constraints[index]? with
    | none => simp [runReplacementTrace, hc] at hrun
    | some c =>
      by_cases hcheck : checkReplacement c current proposed = true
      · simp only [runReplacementTrace, hc, hcheck, ↓reduceIte] at hrun
        exact ih proposed hrun
          (solution_checkReplacement constraints c (List.mem_of_getElem? hc)
            current proposed f hf hcheck)
      · simp [runReplacementTrace, hc, hcheck] at hrun

/-- A compact refutation consists of a checked replacement trace followed by
an explicitly named empty domain. It can be composed with exhaustive branches
using `unsatisfiable_of_branches`. -/
def checkTraceRefutation (constraints : List (Constraint n State)) (current : Domains n State)
    (trace : List (Nat × Domains n State)) (v : Fin n) : Bool :=
  match runReplacementTrace constraints current trace with
  | none => false
  | some result => (result v).isEmpty

theorem checkTraceRefutation_sound (constraints : List (Constraint n State))
    (current : Domains n State) (trace : List (Nat × Domains n State)) (v : Fin n)
    (hcheck : checkTraceRefutation constraints current trace v = true) :
    Unsatisfiable current constraints := by
  cases hrun : runReplacementTrace constraints current trace with
  | none => simp [checkTraceRefutation, hrun] at hcheck
  | some result =>
    have he : result v = [] := by simpa only [checkTraceRefutation, hrun, List.isEmpty_iff] using hcheck
    intro f hf
    exact unsatisfiable_of_empty result constraints v he f
      (runReplacementTrace_preserves constraints current trace result hrun f hf)

end SpectreFinite.FiniteTable
