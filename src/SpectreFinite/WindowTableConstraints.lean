module

public import SpectreFinite.FiniteTablePropagation
public import SpectreFinite.RotatedWindows

@[expose] public section


/-! Literal finite-table CSPs obtained by projecting certified marked-hexagon
windows. Every constraint below is satisfied by the actual field assignment;
no geometric-to-table correspondence is supplied as a callback. -/
namespace SpectreFinite.HexSearch

def subPos (x y : Position) : Position := (x.1-y.1,x.2-y.2)

theorem addPos_subPos (c d x : Position) :
    addPos (addPos c d) (subPos x d) = addPos c x := by
  apply Prod.ext <;> simp only [addPos, subPos] <;> omega

/-- All finite-domain variables lying in the supporting window at `delta`. -/
def windowScope {n : Nat} (positions : Fin n → Position)
    (base : List Position) (delta : Position) : List (Fin n) :=
  (List.finRange n).filter (fun v => decide (subPos (positions v) delta ∈ base))

def windowConstraint {n : Nat} (positions : Fin n → Position)
    (base : List Position) (family : List Patch) (delta : Position) :
    FiniteTable.Constraint n State :=
  { scope := windowScope positions base delta
    rows := family.map (fun p => (windowScope positions base delta).map
      (fun v => patchState p (subPos (positions v) delta))) }

def windowConstraints {n : Nat} (positions : Fin n → Position)
    (base : List Position) (family : List Patch) (centers : List Position) :
    List (FiniteTable.Constraint n State) :=
  centers.map (windowConstraint positions base family)

def fieldAssignment {n : Nat} (positions : Fin n → Position)
    (f : Position → State) (center : Position) : FiniteTable.Assignment n State :=
  fun v => f (addPos center (positions v))

/-- A genuine neighboring window supplies one exact row, including every
scoped variable, even when the variable-position map has repetitions. -/
theorem fieldAssignment_satisfies_constraint {n : Nat} (positions : Fin n → Position)
    (base : List Position) (family : List Patch) (f : Position → State)
    (hfamily : OccurrenceComplete f base family) (center delta : Position) :
    FiniteTable.SatisfiesConstraint (windowConstraint positions base family delta)
      (fieldAssignment positions f center) := by
  apply List.mem_map.mpr
  refine ⟨extract f (addPos center delta) base, hfamily _, ?_⟩
  apply List.map_congr_left
  intro v hv
  have hv' : subPos (positions v) delta ∈ base := by
    exact of_decide_eq_true (List.mem_filter.mp hv).2
  change patchState (restriction (shiftedField f (addPos center delta)) base)
    (subPos (positions v) delta) = f (addPos center (positions v))
  rw [patchState_restriction _ _ _ hv']
  change f (addPos (addPos center delta) (subPos (positions v) delta)) = _
  rw [addPos_subPos]

theorem fieldAssignment_satisfies {n : Nat} (positions : Fin n → Position)
    (base : List Position) (family : List Patch) (f : Position → State)
    (hfamily : OccurrenceComplete f base family) (center : Position)
    (centers : List Position) :
    FiniteTable.Satisfies (windowConstraints positions base family centers)
      (fieldAssignment positions f center) := by
  intro c hc
  obtain ⟨delta, _, rfl⟩ := List.mem_map.mp hc
  exact fieldAssignment_satisfies_constraint positions base family f hfamily center delta

def rootDomains {n : Nat} (positions : Fin n → Position) (root : State) :
    FiniteTable.Domains n State :=
  fun v => if positions v = (0,0) then [root] else stateChoices

theorem fieldAssignment_fits_rootDomains {n : Nat} (positions : Fin n → Position)
    (f : Position → State) (center : Position) :
    FiniteTable.Fits (rootDomains positions (f center)) (fieldAssignment positions f center) := by
  intro v
  by_cases hv : positions v = (0,0)
  · simp [rootDomains, hv, fieldAssignment, addPos]
  · simpa [rootDomains, hv] using mem_stateChoices (fieldAssignment positions f center v)

/-- Actual field windows solve the concrete finite CSP with their actual
root state. The only family hypothesis is the explicit occurrence invariant. -/
theorem fieldAssignment_solution {n : Nat} (positions : Fin n → Position)
    (base : List Position) (family : List Patch) (f : Position → State)
    (hfamily : OccurrenceComplete f base family) (center : Position)
    (centers : List Position) :
    FiniteTable.Solution (rootDomains positions (f center))
      (windowConstraints positions base family centers) (fieldAssignment positions f center) :=
  ⟨fieldAssignment_fits_rootDomains positions f center,
    fieldAssignment_satisfies positions base family f hfamily center centers⟩

/-- A checked finite contradiction excludes the corresponding root in any
field whose small-window family has already been certified. -/
theorem root_excluded_of_unsatisfiable {n : Nat} (positions : Fin n → Position)
    (base : List Position) (family : List Patch) (root : State)
    (centers : List Position)
    (hunsat : FiniteTable.Unsatisfiable (rootDomains positions root)
      (windowConstraints positions base family centers))
    (f : Position → State) (hfamily : OccurrenceComplete f base family)
    (center : Position) : f center ≠ root := by
  intro hroot
  have hsol := fieldAssignment_solution positions base family f hfamily center centers
  rw [hroot] at hsol
  exact hunsat _ hsol

/-- Restrict a finite candidate feature without dropping unspecified states.
Conflicting repeated prescriptions correctly leave an empty domain. -/
def patternDomains {n : Nat} (positions : Fin n → Position) (pattern : Patch) :
    FiniteTable.Domains n State :=
  fun v => stateChoices.filter (fun s => pattern.all
    (fun a => decide (positions v = a.1 → s = a.2)))

theorem fieldAssignment_fits_patternDomains {n : Nat} (positions : Fin n → Position)
    (f : Position → State) (center : Position) (pattern : Patch)
    (hpattern : ∀ a ∈ pattern, f (addPos center a.1) = a.2) :
    FiniteTable.Fits (patternDomains positions pattern) (fieldAssignment positions f center) := by
  intro v
  apply List.mem_filter.mpr
  refine ⟨mem_stateChoices _, ?_⟩
  apply List.all_eq_true.mpr
  intro a ha
  apply decide_eq_true_eq.mpr
  intro hv
  simpa [fieldAssignment, hv] using hpattern a ha

/-- Every checked refutation of a finite prescribed feature transfers to
actual field windows, with all table rows obtained from neighboring windows. -/
theorem pattern_excluded_of_unsatisfiable {n : Nat} (positions : Fin n → Position)
    (base : List Position) (family : List Patch) (pattern : Patch)
    (centers : List Position)
    (hunsat : FiniteTable.Unsatisfiable (patternDomains positions pattern)
      (windowConstraints positions base family centers))
    (f : Position → State) (hfamily : OccurrenceComplete f base family)
    (center : Position) : ¬ (∀ a ∈ pattern, f (addPos center a.1) = a.2) := by
  intro hpattern
  exact hunsat (fieldAssignment positions f center)
    ⟨fieldAssignment_fits_patternDomains positions f center pattern hpattern,
      fieldAssignment_satisfies positions base family f hfamily center centers⟩

end SpectreFinite.HexSearch
