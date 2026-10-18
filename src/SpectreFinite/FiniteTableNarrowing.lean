module

public import SpectreFinite.FiniteTablePropagation

@[expose] public section


/-! Explicit checked domain narrowing. An untrusted generator supplies target
domains; the checker scans every original row compatible with the current
domains and checks all its scoped entries against the proposed domains.
The actual update intersects current domains with these targets. No asserted
domain equality, external solver answer, or row omission is trusted. -/
namespace SpectreFinite.FiniteTable

universe u
variable {n : Nat} {State : Type u} [DecidableEq State]

theorem rowCompatible_projection_iff (domains : Domains n State)
    (f : Assignment n State) (scope : List (Fin n)) :
    rowCompatible domains scope (scope.map f) = true ↔
      ∀ v ∈ scope, f v ∈ domains v := by
  induction scope with
  | nil => simp [rowCompatible]
  | cons v vs ih => simp [rowCompatible, ih]

/-- A finite, executable check of *every* currently compatible table row.
Malformed rows are already incompatible. Repeated scoped variables are checked
at every occurrence. This test is conservative for inconsistent repeated rows. -/
def checkNarrowing (c : Constraint n State) (current proposed : Domains n State) : Bool :=
  c.rows.all (fun row => if rowCompatible current c.scope row then
    rowCompatible proposed c.scope row else true)

/-- Only variables mentioned by this constraint may be changed, and only by
intersection. Proposed domains outside its scope are deliberately ignored. -/
def applyNarrowing (c : Constraint n State) (current proposed : Domains n State) :
    Domains n State :=
  fun v => if v ∈ c.scope then
    (current v).filter (fun s => decide (s ∈ proposed v))
  else current v

theorem applyNarrowing_subset (c : Constraint n State) (current proposed : Domains n State)
    (v : Fin n) (s : State) (hs : s ∈ applyNarrowing c current proposed v) :
    s ∈ current v := by
  unfold applyNarrowing at hs
  split at hs
  · exact (List.mem_filter.mp hs).1
  · exact hs

/-- Soundness of an explicitly proposed narrowing step. The real assignment's
scope projection is among the original rows and is currently compatible, so
the checker necessarily checks it against every proposed scoped domain. -/
theorem applyNarrowing_preserves (c : Constraint n State)
    (current proposed : Domains n State) (f : Assignment n State)
    (hf : Fits current f) (hc : SatisfiesConstraint c f)
    (hcheck : checkNarrowing c current proposed = true) :
    Fits (applyNarrowing c current proposed) f := by
  have hrow := List.all_eq_true.mp hcheck (c.scope.map f) hc
  have hcur := rowCompatible_projection current f hf c.scope
  have hnew : rowCompatible proposed c.scope (c.scope.map f) = true := by
    simpa only [hcur, ↓reduceIte] using hrow
  have hfit := (rowCompatible_projection_iff proposed f c.scope).mp hnew
  intro v
  unfold applyNarrowing
  split
  · rename_i hv
    exact List.mem_filter.mpr ⟨hf v, by simp [hfit v hv]⟩
  · exact hf v

theorem solution_applyNarrowing (constraints : List (Constraint n State))
    (c : Constraint n State) (hc : c ∈ constraints)
    (current proposed : Domains n State) (f : Assignment n State)
    (hf : Solution current constraints f)
    (hcheck : checkNarrowing c current proposed = true) :
    Solution (applyNarrowing c current proposed) constraints f :=
  ⟨applyNarrowing_preserves c current proposed f hf.1 (hf.2 c hc) hcheck, hf.2⟩

theorem unsatisfiable_of_checked_narrowing (constraints : List (Constraint n State))
    (c : Constraint n State) (hc : c ∈ constraints)
    (current proposed : Domains n State)
    (hcheck : checkNarrowing c current proposed = true)
    (hu : Unsatisfiable (applyNarrowing c current proposed) constraints) :
    Unsatisfiable current constraints :=
  fun f hf => hu f (solution_applyNarrowing constraints c hc current proposed f hf hcheck)

end SpectreFinite.FiniteTable
