module

public import Init

@[expose] public section


/-!
Sound finite-table constraint propagation. This module supplies only a generic
certificate engine: no concrete Spectre table is assumed complete.

An assignment satisfies a table exactly when its scope projection is a listed
row. Consequently malformed lengths cannot satisfy it, and repeated scope
variables must have equal entries. Compatibility rejects length mismatches;
support for a variable checks *every* occurrence of that variable. Repetitions
and duplicate rows or domain values are permitted, without a Nodup premise.
-/
namespace SpectreFinite.FiniteTable

universe u
variable {n : Nat} {State : Type u}

abbrev Domains (n : Nat) (State : Type u) := Fin n → List State
abbrev Assignment (n : Nat) (State : Type u) := Fin n → State

structure Constraint (n : Nat) (State : Type u) where
  scope : List (Fin n)
  rows : List (List State)
  deriving Repr

def Fits (domains : Domains n State) (f : Assignment n State) : Prop :=
  ∀ v, f v ∈ domains v

def SatisfiesConstraint (c : Constraint n State) (f : Assignment n State) : Prop :=
  c.scope.map f ∈ c.rows

def Satisfies (constraints : List (Constraint n State)) (f : Assignment n State) : Prop :=
  ∀ c ∈ constraints, SatisfiesConstraint c f

def Solution (domains : Domains n State) (constraints : List (Constraint n State))
    (f : Assignment n State) : Prop :=
  Fits domains f ∧ Satisfies constraints f

def Unsatisfiable (domains : Domains n State)
    (constraints : List (Constraint n State)) : Prop :=
  ∀ f, ¬ Solution domains constraints f

/-- Exact-length, pointwise current-domain compatibility. Repeated variables
may give conservative false positives here; `rowSupports` checks all their
occurrences together when filtering their domain. Neither test loses solutions. -/
def rowCompatible [DecidableEq State] (domains : Domains n State) :
    List (Fin n) → List State → Bool
  | [], [] => true
  | v :: vs, s :: ss => decide (s ∈ domains v) && rowCompatible domains vs ss
  | _, _ => false

/-- A row supports value `s` at every occurrence of `v`. Length mismatches fail.
If `v` is absent, this predicate is vacuously true for exact-length rows. -/
def rowSupports [DecidableEq State] (v : Fin n) (s : State) :
    List (Fin n) → List State → Bool
  | [], [] => true
  | w :: ws, t :: ts => decide (w = v → t = s) && rowSupports v s ws ts
  | _, _ => false

theorem rowCompatible_projection [DecidableEq State] (domains : Domains n State)
    (f : Assignment n State) (hf : Fits domains f) (scope : List (Fin n)) :
    rowCompatible domains scope (scope.map f) = true := by
  induction scope with
  | nil => rfl
  | cons v vs ih => simp [rowCompatible, hf v, ih]

theorem rowSupports_projection [DecidableEq State] (f : Assignment n State)
    (v : Fin n) (scope : List (Fin n)) :
    rowSupports v (f v) scope (scope.map f) = true := by
  induction scope with
  | nil => rfl
  | cons w ws ih =>
    by_cases h : w = v
    · simp [rowSupports, h, ih]
    · simp [rowSupports, h, ih]

/-- First select compatible rows, then intersect each involved variable's
current domain with values supported by one of those rows. All variables use
the same input domains. Variables outside the scope are unchanged. -/
def filterConstraint [DecidableEq State] (c : Constraint n State)
    (domains : Domains n State) : Domains n State :=
  let viable := c.rows.filter (rowCompatible domains c.scope)
  fun v => if v ∈ c.scope then
    (domains v).filter (fun s => viable.any (rowSupports v s c.scope))
  else domains v

theorem filterConstraint_subset [DecidableEq State] (c : Constraint n State)
    (domains : Domains n State) (v : Fin n) (s : State)
    (hs : s ∈ filterConstraint c domains v) : s ∈ domains v := by
  unfold filterConstraint at hs
  split at hs
  · exact (List.mem_filter.mp hs).1
  · exact hs

/-- Main local invariant: no value used by a satisfying full assignment is
removed by a table propagation step. -/
theorem filterConstraint_preserves [DecidableEq State] (c : Constraint n State)
    (domains : Domains n State) (f : Assignment n State)
    (hf : Fits domains f) (hc : SatisfiesConstraint c f) :
    Fits (filterConstraint c domains) f := by
  intro v
  unfold filterConstraint
  split
  · apply List.mem_filter.mpr
    refine ⟨hf v, List.any_eq_true.mpr ?_⟩
    exact ⟨c.scope.map f, List.mem_filter.mpr
      ⟨hc, rowCompatible_projection domains f hf c.scope⟩,
      rowSupports_projection f v c.scope⟩
  · exact hf v

/-- A finite sequence of constraints, evaluated left to right. -/
def propagate [DecidableEq State] :
    List (Constraint n State) → Domains n State → Domains n State
  | [], domains => domains
  | c :: cs, domains => propagate cs (filterConstraint c domains)

theorem propagate_preserves [DecidableEq State]
    (schedule : List (Constraint n State)) (domains : Domains n State)
    (f : Assignment n State) (hf : Fits domains f) (hs : Satisfies schedule f) :
    Fits (propagate schedule domains) f := by
  induction schedule generalizing domains with
  | nil => exact hf
  | cons c cs ih =>
    exact ih (filterConstraint c domains)
      (filterConstraint_preserves c domains f hf (hs c (by simp)))
      (fun d hd => hs d (List.mem_cons_of_mem c hd))

/-- A requested finite number of full passes; no fixed-point assertion is
needed to obtain a sound result. -/
def propagateIter [DecidableEq State] (constraints : List (Constraint n State)) :
    Nat → Domains n State → Domains n State
  | 0, domains => domains
  | rounds + 1, domains => propagateIter constraints rounds (propagate constraints domains)

theorem propagateIter_preserves [DecidableEq State]
    (constraints : List (Constraint n State)) (rounds : Nat)
    (domains : Domains n State) (f : Assignment n State)
    (hf : Fits domains f) (hs : Satisfies constraints f) :
    Fits (propagateIter constraints rounds domains) f := by
  induction rounds generalizing domains with
  | zero => exact hf
  | succ rounds ih => exact ih _ (propagate_preserves constraints domains f hf hs)

theorem solution_propagateIter [DecidableEq State]
    (constraints : List (Constraint n State)) (rounds : Nat)
    (domains : Domains n State) (f : Assignment n State)
    (hf : Solution domains constraints f) :
    Solution (propagateIter constraints rounds domains) constraints f :=
  ⟨propagateIter_preserves constraints rounds domains f hf.1 hf.2, hf.2⟩

theorem unsatisfiable_of_empty (domains : Domains n State)
    (constraints : List (Constraint n State)) (v : Fin n) (he : domains v = []) :
    Unsatisfiable domains constraints := by
  intro f hf
  have hv := hf.1 v
  rw [he] at hv
  exact List.not_mem_nil hv

theorem unsatisfiable_of_propagateIter [DecidableEq State]
    (constraints : List (Constraint n State)) (rounds : Nat)
    (domains : Domains n State)
    (hu : Unsatisfiable (propagateIter constraints rounds domains) constraints) :
    Unsatisfiable domains constraints :=
  fun f hf => hu f (solution_propagateIter constraints rounds domains f hf)

theorem unsatisfiable_of_propagated_empty [DecidableEq State]
    (constraints : List (Constraint n State)) (rounds : Nat)
    (domains : Domains n State) (v : Fin n)
    (he : propagateIter constraints rounds domains v = []) :
    Unsatisfiable domains constraints :=
  unsatisfiable_of_propagateIter constraints rounds domains
    (unsatisfiable_of_empty _ constraints v he)

/-- Fix one branch variable to a chosen value. The branch rule below requires
coverage of *every* value of its current domain. -/
def restrict (domains : Domains n State) (v : Fin n) (s : State) : Domains n State :=
  fun w => if w = v then [s] else domains w

theorem fits_restrict (domains : Domains n State) (f : Assignment n State)
    (hf : Fits domains f) (v : Fin n) : Fits (restrict domains v (f v)) f := by
  intro w
  unfold restrict
  split
  · rename_i h
    simp [h]
  · exact hf w

/-- Exhaustive finite branching. Duplicate domain values cause no problem;
an empty domain makes the premise vacuous and the conclusion remains valid. -/
theorem unsatisfiable_of_branches (domains : Domains n State)
    (constraints : List (Constraint n State)) (v : Fin n)
    (hb : ∀ s ∈ domains v, Unsatisfiable (restrict domains v s) constraints) :
    Unsatisfiable domains constraints := by
  intro f hf
  exact hb (f v) (hf.1 v) f ⟨fits_restrict domains f hf.1 v, hf.2⟩

end SpectreFinite.FiniteTable
