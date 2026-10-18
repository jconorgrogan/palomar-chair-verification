module

public import SpectreGeometry.HalfplaneCertificateData
public import SpectreGeometry.TriangleGeometry

@[expose] public section


/-! Real soundness of the exact BSP certificates. Successful checking proves
both region inclusion and all branch coverage; no geometric oracle is assumed. -/
namespace SpectreGeometry.HalfplaneCertificate
noncomputable section

def evalConstraint (c : Constraint) (x : RealPoint) : ℝ :=
  (c.1 : ℝ)*x.1+(c.2.1 : ℝ)*x.2+(c.2.2 : ℝ)
def Satisfies (hypotheses : List Constraint) (x : RealPoint) : Prop :=
  ∀ c ∈ hypotheses, 0 ≤ evalConstraint c x

theorem eval_zero (x : RealPoint) : evalConstraint zeroConstraint x=0 := by
  simp [evalConstraint,zeroConstraint]

theorem eval_add (a b : Constraint) (x : RealPoint) :
    evalConstraint (addConstraint a b) x=evalConstraint a x+evalConstraint b x := by
  simp only [evalConstraint,addConstraint,Int.cast_add]
  ring

theorem eval_neg (a : Constraint) (x : RealPoint) :
    evalConstraint (negConstraint a) x= -evalConstraint a x := by
  simp only [evalConstraint,negConstraint,Int.cast_neg]
  ring

theorem eval_scale (n : Nat) (a : Constraint) (x : RealPoint) :
    evalConstraint (scaleConstraint n a) x=(n : ℝ)*evalConstraint a x := by
  simp only [evalConstraint,scaleConstraint,Int.cast_mul,Int.cast_natCast]
  ring

theorem lookup_nonnegative (hypotheses : List Constraint) (x : RealPoint)
    (h : Satisfies hypotheses x) (i : Nat) : 0 ≤ evalConstraint (lookupConstraint hypotheses i) x := by
  induction hypotheses generalizing i with
  | nil => simp [lookupConstraint,eval_zero]
  | cons a as ih =>
      cases i with
      | zero => exact h a (by simp)
      | succ i => exact ih (fun c hc => h c (by simp [hc])) i

theorem combine_nonnegative (hypotheses : List Constraint) (weights : SparseWeights) (x : RealPoint)
    (h : Satisfies hypotheses x) : 0 ≤ evalConstraint (combine hypotheses weights) x := by
  induction weights with
  | nil => simp [combine,eval_zero]
  | cons iw ws ih =>
      rcases iw with ⟨i,w⟩
      rw [combine,eval_add,eval_scale]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg w) (lookup_nonnegative hypotheses x h i)) ih

theorem checkFacet_sound (hypotheses : List Constraint) (goal : Constraint) (w : FacetWitness)
    (hcheck : checkFacet hypotheses goal w=true) (x : RealPoint) (hx : Satisfies hypotheses x) :
    0 ≤ evalConstraint goal x := by
  simp only [checkFacet,Bool.and_eq_true,decide_eq_true_eq] at hcheck
  have h := combine_nonnegative hypotheses w.weights x hx
  rw [hcheck.2,eval_scale] at h
  exact nonneg_of_mul_nonneg_right h (by exact_mod_cast hcheck.1)

theorem checkFacets_sound (hypotheses goals : List Constraint) (ws : List FacetWitness)
    (hcheck : checkFacets hypotheses goals ws=true) (x : RealPoint) (hx : Satisfies hypotheses x) :
    Satisfies goals x := by
  induction goals generalizing ws with
  | nil => intro c hc; simp at hc
  | cons goal goals ih =>
      cases ws with
      | nil => simp [checkFacets] at hcheck
      | cons w ws =>
          simp only [checkFacets,Bool.and_eq_true] at hcheck
          intro c hc
          rcases List.mem_cons.mp hc with hc | hc
          · subst c
            exact checkFacet_sound hypotheses goal w hcheck.1 x hx
          · exact ih ws hcheck.2 c hc

theorem satisfies_append_facet (hypotheses : List Constraint) (c : Constraint) (x : RealPoint)
    (hx : Satisfies hypotheses x) (hc : 0 ≤ evalConstraint c x) :
    Satisfies (hypotheses++[c]) x := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact hx d hd
  · have he : d=c := by simpa using hd
    rwa [he]

theorem checkTree_sound (hypotheses : List Constraint) (targets : List (List Constraint))
    (tree : CoverTree) (hcheck : checkTree hypotheses targets tree=true)
    (x : RealPoint) (hx : Satisfies hypotheses x) :
    ∃ target : Nat, target<targets.length ∧ Satisfies (targets.getD target []) x := by
  induction tree generalizing hypotheses with
  | leaf target ws =>
      simp only [checkTree,Bool.and_eq_true,decide_eq_true_eq] at hcheck
      exact ⟨target,hcheck.1,checkFacets_sound hypotheses _ ws hcheck.2 x hx⟩
  | split line pos neg ihpos ihneg =>
      simp only [checkTree,Bool.and_eq_true] at hcheck
      by_cases hp : 0 ≤ evalConstraint line x
      · exact ihpos _ hcheck.1 (satisfies_append_facet hypotheses line x hx hp)
      · exact ihneg _ hcheck.2 (satisfies_append_facet hypotheses (negConstraint line) x hx
          (by rw [eval_neg]; exact neg_nonneg.2 (le_of_not_ge hp)))
  | empty ws =>
      simp only [checkTree,decide_eq_true_eq] at hcheck
      have h := combine_nonnegative hypotheses ws x hx
      rw [hcheck] at h
      norm_num [evalConstraint] at h

end
end SpectreGeometry.HalfplaneCertificate
