module

public import ClarkSeed.ProfileMating
public import ProductClosure.ProductGraphCandidateClosure

@[expose] public section

/-! Sparse literal profile preservation along actual native contact walks.
The sole profile premise is matching under each original generator at every
actual matched site. Candidate matching and odd path parity are conclusions. -/
namespace ClarkSeed.OddWalkProfiles
noncomputable section
open ProductClosure ProductClosure.NativeCompiler
open ProductClosure.ProductGraphContactWalks ProductClosure.ProductGraphCandidateClosure
open ProfileMating
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m+1))}
variable (E : Finset (Space m ≃ᵢ Space m)) (hE : ∀ g ∈ E, IsProperPlacement g)
variable (P : Site S → Profile (Space m))

/-- The recovered sparse profile law is required only on the input generators;
all native tangent frames and all exposed facets are quantified literally. -/
def GeneratorProfiles : Prop :=
  ∀ g ∈ E, ∀ u v : Site S, SiteTransport g u v →
    P u = mate g.toEquiv (P v)

theorem edge_profile (hP : GeneratorProfiles E P) {u v : Site S}
    (h : (contactGraph E hE).Adj u v) :
    P u = mate (edgePlacement E hE u v h).toEquiv (P v) := by
  obtain ⟨hm, ht⟩ := edgePlacement_spec E hE u v h
  rcases hm with hm | hm
  · exact hP _ hm u v ht
  · have hi := hP _ hm v u (inverse_siteTransport ht)
    exact (mate_eq_inverse_iff (edgePlacement E hE u v h).toEquiv (P u) (P v)).mpr hi

/-- A length-n path transports vertices by its actual composed isometry and
flips the material bit exactly n times. -/
theorem walk_profile (hP : GeneratorProfiles E P) {u v : Site S}
    (w : (contactGraph E hE).Walk u v) :
    P u = move (walkPlacement E hE w).toEquiv (ProfileMating.flip^[w.length] (P v)) := by
  induction w with
  | @nil u =>
    change P u = move (Equiv.refl _) (P u)
    exact (move_refl (P u)).symm
  | @cons u v z h w ih =>
    calc
      P u = mate (edgePlacement E hE u v h).toEquiv (P v) := edge_profile E hE P hP h
      _ = move (edgePlacement E hE u v h).toEquiv
          (ProfileMating.flip (move (walkPlacement E hE w).toEquiv (ProfileMating.flip^[w.length] (P z)))) := by
        rw [ih]
        rfl
      _ = move (edgePlacement E hE u v h).toEquiv
          (move (walkPlacement E hE w).toEquiv (ProfileMating.flip (ProfileMating.flip^[w.length] (P z)))) := by
        rw [flip_move]
      _ = move (walkPlacement E hE (.cons h w)).toEquiv
          (ProfileMating.flip^[(SimpleGraph.Walk.cons h w).length] (P z)) := by
        rw [move_trans, SimpleGraph.Walk.length_cons, Function.iterate_succ_apply']
        rfl

/-- Odd paths recover exactly the original one-flip mating action. -/
theorem odd_walk_profile (hP : GeneratorProfiles E P) {u v : Site S}
    (w : (contactGraph E hE).Walk u v) (hw : Odd w.length) :
    P u = mate (walkPlacement E hE w).toEquiv (P v) := by
  rw [walk_profile E hE P hP w, flip_iterate_odd _ hw]
  rfl

/-- Literal compiled opposition recovers original sparse mating at the actual
candidate isometry, with no candidate-group or all-profile assumption. -/
theorem matched_coefficients_profile [LinearOrder (Site S)]
    (hP : GeneratorProfiles E P) (g : Space m ≃ᵢ Space m)
    (u v : Site S) (ht : SiteTransport g u v)
    (hc : (graphCoefficients (contactGraph E hE)).value v =
      -(graphCoefficients (contactGraph E hE)).value u) :
    P u = mate g.toEquiv (P v) := by
  obtain ⟨w,hw,htw,_⟩ := opposite_coefficients_odd_transport E hE u v hc
  have hg : g = walkPlacement E hE w := isometry_eq_of_siteTransport ht htw
  rw [hg]
  exact odd_walk_profile E hE P hP w hw

/-- The universal native coefficient equations force sparse profiles at every
actual matched site, not merely at the site used for initial registration. -/
theorem fullProfile_sparse_profiles [LinearOrder (Site S)]
    (hP : GeneratorProfiles E P) (g : Space m ≃ᵢ Space m)
    (hf : FullProfileMating (graphCoefficients (contactGraph (S := S) E hE)) g) :
    ∀ u v : Site S, SiteTransport g u v → P u = mate g.toEquiv (P v) := by
  intro u v ht
  exact matched_coefficients_profile E hE P hP g u v ht (hf u v ht)

#print axioms walk_profile
#print axioms odd_walk_profile
#print axioms matched_coefficients_profile
#print axioms fullProfile_sparse_profiles
end
end ClarkSeed.OddWalkProfiles
