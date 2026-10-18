module

public import SpectreFinite.FiniteTableReplacement

@[expose] public section


/-! Finite-output coverage certificates for table CSPs. An accepted tree
proves that every satisfying assignment's full ordered projection belongs to
the declared finite output list. It does NOT assert that every listed output
is satisfying, nor that any satisfying assignment exists. -/
namespace SpectreFinite.FiniteTable

universe u
variable {n : Nat} {State : Type u}

/-- Canonical full projection, with each variable appearing in increasing order. -/
def fullProjection (f : Assignment n State) : List State := (List.finRange n).map f

def Covers (domains : Domains n State) (constraints : List (Constraint n State))
    (outputs : List (List State)) : Prop :=
  ∀ f, Solution domains constraints f → fullProjection f ∈ outputs

/-- Exact-length singleton containment. Each scoped domain must be a subset
of the singleton containing its paired row entry; empty domains are allowed.
A malformed row length fails rather than being silently truncated. -/
def rowCovers [DecidableEq State] (domains : Domains n State) :
    List (Fin n) → List State → Bool
  | [], [] => true
  | v :: vs, s :: ss => (domains v).all (fun t => decide (t = s)) && rowCovers domains vs ss
  | _, _ => false

theorem rowCovers_projection [DecidableEq State] (domains : Domains n State)
    (scope : List (Fin n)) (row : List State)
    (hcheck : rowCovers domains scope row = true)
    (f : Assignment n State) (hf : Fits domains f) : scope.map f = row := by
  induction scope generalizing row with
  | nil =>
    cases row with
    | nil => rfl
    | cons s ss => simp [rowCovers] at hcheck
  | cons v vs ih =>
    cases row with
    | nil => simp [rowCovers] at hcheck
    | cons s ss =>
      have hparts := Bool.and_eq_true_iff.mp hcheck
      have hv : f v = s := of_decide_eq_true (List.all_eq_true.mp hparts.1 (f v) (hf v))
      simp only [List.map_cons, hv, ih ss hparts.2]

/-- Cover leaves either exhibit an empty domain or name a row in the declared
output list. All intermediate reductions remain kernel-checked. -/
inductive CoverCertificate (n : Nat) (State : Type u) where
  | empty (v : Fin n)
  | output (rowIndex : Nat)
  | propagation (rounds : Nat) (next : CoverCertificate n State)
  | narrowing (constraintIndex : Nat) (proposed : Domains n State)
      (next : CoverCertificate n State)
  | replacements (trace : List (Nat × Domains n State)) (next : CoverCertificate n State)
  | branch (v : Fin n) (children : List (CoverCertificate n State))

def checkCoverBranches (checkChild : State → CoverCertificate n State → Bool) :
    List State → List (CoverCertificate n State) → Bool
  | [], [] => true
  | s :: ss, child :: children =>
      checkChild s child && checkCoverBranches checkChild ss children
  | _, _ => false

theorem checkCoverBranches_covers (checkChild : State → CoverCertificate n State → Bool)
    (values : List State) (children : List (CoverCertificate n State))
    (hcheck : checkCoverBranches checkChild values children = true) :
    ∀ s ∈ values, ∃ child, checkChild s child = true := by
  induction values generalizing children with
  | nil => simp
  | cons s ss ih =>
    cases children with
    | nil => simp [checkCoverBranches] at hcheck
    | cons child children =>
      have hparts := Bool.and_eq_true_iff.mp hcheck
      intro t ht
      rcases List.mem_cons.mp ht with h | h
      · subst t
        exact ⟨child, hparts.1⟩
      · exact ih children hparts.2 t h

/-- Finite depth budget, exact branch coverage, checked original-constraint
indices, and checked declared-output indices. Failure gives no conclusion. -/
def checkCover [DecidableEq State] : Nat → List (Constraint n State) →
    List (List State) → Domains n State → CoverCertificate n State → Bool
  | 0, _, _, _, _ => false
  | depth + 1, constraints, outputs, domains, certificate =>
    match certificate with
    | .empty v => (domains v).isEmpty
    | .output index =>
        match outputs[index]? with
        | none => false
        | some row => rowCovers domains (List.finRange n) row
    | .propagation rounds next =>
        checkCover depth constraints outputs (propagateIter constraints rounds domains) next
    | .narrowing index proposed next =>
        match constraints[index]? with
        | none => false
        | some c => checkNarrowing c domains proposed &&
            checkCover depth constraints outputs (applyNarrowing c domains proposed) next
    | .replacements trace next =>
        match runReplacementTrace constraints domains trace with
        | none => false
        | some result => checkCover depth constraints outputs result next
    | .branch v children =>
        checkCoverBranches
          (fun s child => checkCover depth constraints outputs (restrict domains v s) child)
          (domains v) children

/-- Main coverage theorem. Every satisfying assignment survives the certified
reductions and follows its own value at each exhaustive split, until it reaches
a declared row whose entries contain all its remaining domain values. -/
theorem checkCover_sound [DecidableEq State] (depth : Nat)
    (constraints : List (Constraint n State)) (outputs : List (List State))
    (domains : Domains n State) (certificate : CoverCertificate n State)
    (hcheck : checkCover depth constraints outputs domains certificate = true) :
    Covers domains constraints outputs := by
  induction depth generalizing domains certificate with
  | zero => simp [checkCover] at hcheck
  | succ depth ih =>
    intro f hf
    cases certificate with
    | empty v =>
      exact False.elim
        (unsatisfiable_of_empty domains constraints v (List.isEmpty_iff.mp hcheck) f hf)
    | output index =>
      cases hout : outputs[index]? with
      | none => simp [checkCover, hout] at hcheck
      | some row =>
        have hr : rowCovers domains (List.finRange n) row = true := by
          simpa only [checkCover, hout] using hcheck
        have he : fullProjection f = row := rowCovers_projection domains _ row hr f hf.1
        rw [he]
        exact List.mem_of_getElem? hout
    | propagation rounds next =>
      exact ih _ next hcheck f (solution_propagateIter constraints rounds domains f hf)
    | narrowing index proposed next =>
      cases hc : constraints[index]? with
      | none => simp [checkCover, hc] at hcheck
      | some c =>
        have hparts : checkNarrowing c domains proposed = true ∧
            checkCover depth constraints outputs (applyNarrowing c domains proposed) next = true := by
          simpa only [checkCover, hc, Bool.and_eq_true] using hcheck
        exact ih _ next hparts.2 f
          (solution_applyNarrowing constraints c (List.mem_of_getElem? hc)
            domains proposed f hf hparts.1)
    | replacements trace next =>
      cases hrun : runReplacementTrace constraints domains trace with
      | none => simp [checkCover, hrun] at hcheck
      | some result =>
        have hr : checkCover depth constraints outputs result next = true := by
          simpa only [checkCover, hrun] using hcheck
        exact ih result next hr f
          (runReplacementTrace_preserves constraints domains trace result hrun f hf)
    | branch v children =>
      obtain ⟨child, hchild⟩ :=
        checkCoverBranches_covers _ (domains v) children hcheck (f v) (hf.1 v)
      exact ih _ child hchild f ⟨fits_restrict domains f hf.1 v, hf.2⟩

end SpectreFinite.FiniteTable
