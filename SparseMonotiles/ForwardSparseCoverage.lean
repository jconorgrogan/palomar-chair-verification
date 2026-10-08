module
public import SparseMonotiles.ForwardContactCertificatesFields
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Necessary box-gap conditions for facet contact. Each coordinate is at
most two units apart, and at most one coordinate can exceed one unit. -/
def ForwardBoxSafe {d : ℕ} (p q : Pose d) : Prop :=
  (∀ j : Fin d, ¬ ForwardGap (boxLower p j) (boxLower q j) 2) ∧
  (∀ j k : Fin d, ForwardGap (boxLower p j) (boxLower q j) 1 →
    ForwardGap (boxLower p k) (boxLower q k) 1 → j = k)

/-- Geometric completeness of the box-gap filter, without enumeration. -/
theorem cellContact_forwardBoxSafe {d : ℕ} {p q : Pose d}
    (h : CellContact p q) : ForwardBoxSafe p q := by
  constructor
  · intro j hj
    exact forward_far_noncontact j hj h
  · intro j k hj hk
    by_contra hne
    exact forward_two_gap_noncontact j k hne hj hk h

def forwardBoxSafeB (d : ℕ) (p q : CoarseFields) : Bool :=
  decide ((∀ j : Fin d, ¬ ForwardGap (p.lower j.val) (q.lower j.val) 2) ∧
    (∀ j k : Fin d, ForwardGap (p.lower j.val) (q.lower j.val) 1 →
      ForwardGap (p.lower k.val) (q.lower k.val) 1 → j = k))

theorem forwardBoxSafeB_iff {d : ℕ} {pc qc : CoarseFields} {p q : Pose d}
    (hp : pc.Represents p) (hq : qc.Represents q) :
    forwardBoxSafeB d pc qc = true ↔ ForwardBoxSafe p q := by
  simp only [forwardBoxSafeB, decide_eq_true_eq, ForwardBoxSafe,
    CoarseFields.lower_eq hp, CoarseFields.lower_eq hq]

theorem cellContact_forwardBoxSafeB {d : ℕ} {pc qc : CoarseFields} {p q : Pose d}
    (hp : pc.Represents p) (hq : qc.Represents q) (h : CellContact p q) :
    forwardBoxSafeB d pc qc = true :=
  (forwardBoxSafeB_iff hp hq).mpr (cellContact_forwardBoxSafe h)

/-- A checked finite coverage claim. The supplied retained roles may be
sparse, but every source role is required to pass this implication. -/
def forwardCoverageB {ι : Type} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (root : CoarseFields) (source : ι → CoarseFields)
    (retained : Finset ι) : Bool :=
  decide (∀ n, forwardBoxSafeB d root (source n) = true → n ∈ retained)

theorem forwardCoverageB_sound {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {root : Pose d} {sources : ι → Pose d} {rootFields : CoarseFields}
    {sourceFields : ι → CoarseFields} {retained : Finset ι}
    (hr : rootFields.Represents root) (hs : ∀ n, (sourceFields n).Represents (sources n))
    (hchecked : forwardCoverageB d rootFields sourceFields retained = true)
    (n : ι) (hc : CellContact root (sources n)) : n ∈ retained := by
  have hcoverage : ∀ n, forwardBoxSafeB d rootFields (sourceFields n) = true →
      n ∈ retained := of_decide_eq_true hchecked
  exact hcoverage n (cellContact_forwardBoxSafeB hr (hs n) hc)

/-- Assembly from checked coverage plus proofs only for retained roles. -/
theorem sparseForward_assemble {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {root : Pose d} {sources : ι → Pose d} {rootFields : CoarseFields}
    {sourceFields : ι → CoarseFields} {retained : Finset ι} {M : Set (Pose d)}
    (hr : rootFields.Represents root) (hs : ∀ n, (sourceFields n).Represents (sources n))
    (hchecked : forwardCoverageB d rootFields sourceFields retained = true)
    (hmembers : ∀ n ∈ retained, normalize root (sources n) ∈ M)
    (n : ι) (hc : CellContact root (sources n)) : normalize root (sources n) ∈ M :=
  hmembers n (forwardCoverageB_sound hr hs hchecked n hc)

theorem sparseForward_excluded_noncontact {d : ℕ} {ι : Type}
    [Fintype ι] [DecidableEq ι]
    {root : Pose d} {sources : ι → Pose d} {rootFields : CoarseFields}
    {sourceFields : ι → CoarseFields} {retained : Finset ι}
    (hr : rootFields.Represents root) (hs : ∀ n, (sourceFields n).Represents (sources n))
    (hchecked : forwardCoverageB d rootFields sourceFields retained = true)
    (n : ι) (hn : n ∉ retained) : ¬ CellContact root (sources n) := by
  intro hc
  exact hn (forwardCoverageB_sound hr hs hchecked n hc)

#print axioms cellContact_forwardBoxSafe
#print axioms forwardBoxSafeB_iff
#print axioms forwardCoverageB_sound
#print axioms sparseForward_assemble
#print axioms sparseForward_excluded_noncontact
end SparseMonotiles.CarrierHierarchy
