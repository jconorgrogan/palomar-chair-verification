module

public import SparseMonotiles.GeneratorRowCoverage

@[expose] public section

/-!
A Boolean, coordinate-local refinement of the pair-to-row certificate checker.
It checks the raw generator fields against the proposed replay pose, and proves
that these fields force `pairPose = some pose`. No generator run or row coverage
is assumed. This avoids constructing dependent pose-equality decisions and
large nested decidability proofs in each concrete coordinate comparison.
-/
namespace SparseMonotiles.Contact

/-- Forward and inverse axes, signs, and undivided translations are sufficient
to check a proposed generator result, including the integrality test. -/
def pairFieldsMatchB {d : ℕ} (den : ℤ) (a b : Facet d)
    (root source : BoxKey d) (p : Pose d) : Bool :=
  (List.finRange d).all fun i =>
    decide (pairAxis a b root source i = p.perm i) &&
    decide (pairAxis b a source root i = p.perm.symm i) &&
    decide (pairSign a b root source i = p.sign i) &&
    decide (pairNumerator a b root source i = den * p.shift i)

/-- A kernel-checked Boolean field comparison implies the actual generator
returns the proposed pose; this is a refinement proof of the executable check. -/
theorem pairFieldsMatchB_sound {d : ℕ} {den : ℤ} (den_ne : den ≠ 0)
    {a b : Facet d} {root source : BoxKey d} {p : Pose d}
    (h : pairFieldsMatchB den a b root source p = true) :
    pairPose den a b root source = some p := by
  have hf : ∀ i, pairAxis a b root source i = p.perm i ∧
      pairAxis b a source root i = p.perm.symm i ∧
      pairSign a b root source i = p.sign i ∧
      pairNumerator a b root source i = den * p.shift i := by
    simpa [pairFieldsMatchB, List.all_eq_true, and_assoc] using h
  have haxes : pairAxis a b root source = p.perm := funext fun i => (hf i).1
  have hinverse : pairAxis b a source root = p.perm.symm := funext fun i => (hf i).2.1
  have hsign : pairSign a b root source = p.sign := funext fun i => (hf i).2.2.1
  have hnum : pairNumerator a b root source = fun i => den * p.shift i :=
    funext fun i => (hf i).2.2.2
  have hready : PairReady den a b root source := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simp only [haxes, hinverse, Equiv.symm_apply_apply]
    · intro i
      simp only [haxes, hinverse, Equiv.apply_symm_apply]
    · intro i
      rw [hsign]
      cases hp : p.negative i <;> simp [Pose.sign, hp]
    · intro i
      rw [hnum]
      exact dvd_mul_right den (p.shift i)
  unfold pairPose
  rw [dif_pos hready]
  congr 1
  apply Pose.eq_of_sameCoordinates
  intro i
  refine ⟨congrFun haxes i, ?_, ?_⟩
  · simp only [pairNegative, hsign]
    cases hp : p.negative i <;> simp [Pose.sign, hp]
  · change pairNumerator a b root source i / den = p.shift i
    rw [hnum]
    exact Int.mul_ediv_cancel_left (p.shift i) den_ne

/-- The overlap branch remains an explicit two-cell certificate. The row branch
checks only raw coordinates and uses `pairFieldsMatchB_sound` for its meaning. -/
def KeyIndexing.pairCertificateB {d n m : ℕ} {ρ : Type*} {g : IndexedGeometry d n}
    (keys : KeyIndexing g m) (lookup : ρ → Pose d) (a b : Fin m) :
    GeneratorPairCertificate d ρ → Bool
  | .absent => decide (keys.pair a b = none)
  | .row address => pairFieldsMatchB g.denominator
      (g.facet (keys.facet a)) (g.facet (keys.facet b))
      (keys.key a) (keys.key b) (lookup address)
  | .overlap root source => decide
      (GeneratorPairCertificate.ChairValid lookup (keys.pair a b)
        (.overlap root source))

theorem KeyIndexing.pairCertificateB_sound {d n m : ℕ} {ρ : Type*}
    {g : IndexedGeometry d n} (den_ne : g.denominator ≠ 0)
    (keys : KeyIndexing g m) (lookup : ρ → Pose d) {a b : Fin m}
    {cert : GeneratorPairCertificate d ρ}
    (h : keys.pairCertificateB lookup a b cert = true) :
    cert.ChairValid lookup (keys.pair a b) := by
  cases cert with
  | absent => exact of_decide_eq_true h
  | overlap root source => exact of_decide_eq_true h
  | row address =>
      have he := pairFieldsMatchB_sound den_ne h
      change optionPoseMatches (keys.pair a b) (lookup address)
      rw [show keys.pair a b = some (lookup address) from he]
      intro i
      exact ⟨rfl, rfl, rfl⟩

/-- Small rectangular blocks are checked as a Boolean list scan. Extraction of
any individual entry is proved independently of the concrete table. -/
def allPairsB {a b : ℕ} (check : Fin a → Fin b → Bool) : Bool :=
  (List.finRange a).all fun i => (List.finRange b).all fun j => check i j

theorem allPairsB_sound {a b : ℕ} {check : Fin a → Fin b → Bool}
    (h : allPairsB check = true) (i : Fin a) (j : Fin b) : check i j = true := by
  exact List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j
    (List.mem_finRange j)

#print axioms pairFieldsMatchB_sound
#print axioms KeyIndexing.pairCertificateB_sound
#print axioms allPairsB_sound
end SparseMonotiles.Contact
