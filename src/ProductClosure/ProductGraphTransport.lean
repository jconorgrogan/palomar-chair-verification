module

public import ProductClosure.ProductGraphEquations
public import ProductClosure.NativeOrientation

@[expose] public section

/-!
# Odd-walk affine transport and forced passive-block identity

Each graph edge is supplied with its actual affine facet transport. Composing
an odd walk transports the entire tangent frame, reverses the normal, and
matches the center. A candidate affine mate with opposite literal component
coefficients must equal this composition. Therefore passive pointwise fixation
is a conclusion, not a restriction placed on the candidate.
-/
namespace ProductClosure.ProductGraphTransport
noncomputable section
open PhysicalRegistration.ComponentCoefficients ProductGraph NativeCompiler

variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m+1))}
abbrev Pose (m : ℕ) := Space m ≃ᵃ[ℝ] Space m

/-- The native full frame determines every ambient linear map. -/
theorem linear_eq_of_native_frame (u : Site S) (L M : Space m →ₗ[ℝ] Space m)
    (ht : ∀ j, L (siteAxis u j) = M (siteAxis u j))
    (hn : L (outward u.1) = M (outward u.1)) : L = M := by
  have hf : frameMatrix u * (frameMatrix u).transpose = 1 :=
    mul_eq_one_comm.mp (frameMatrix_transpose_mul u)
  have hm : ambientMatrix L * frameMatrix u = ambientMatrix M * frameMatrix u := by
    rw [ambientMatrix_mul_frame, ambientMatrix_mul_frame]
    ext i j
    induction j using Fin.lastCases with
    | last => simpa only [fullFrame_last] using congrArg (fun x : Space m => x i) hn
    | cast j => simpa only [fullFrame_castSucc] using congrArg (fun x : Space m => x i) (ht j)
  apply (LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin (m+1)))
    (PiLp.basisFun 2 ℝ (Fin (m+1)))).injective
  change ambientMatrix L = ambientMatrix M
  calc
    ambientMatrix L = (ambientMatrix L * frameMatrix u) * (frameMatrix u).transpose := by
      rw [Matrix.mul_assoc, hf, Matrix.mul_one]
    _ = (ambientMatrix M * frameMatrix u) * (frameMatrix u).transpose := by rw [hm]
    _ = ambientMatrix M := by rw [Matrix.mul_assoc, hf, Matrix.mul_one]

/-- Matching all tangent columns, the normal, and one point determines the
entire affine pose, not merely its action at the selected site. -/
theorem pose_eq_of_native_frame (u : Site S) (g h : Pose m)
    (ht : ∀ j, g.linear (siteAxis u j) = h.linear (siteAxis u j))
    (hn : g.linear (outward u.1) = h.linear (outward u.1))
    (hc : g (siteCenter u) = h (siteCenter u)) : g = h := by
  apply AffineEquiv.toAffineMap_injective
  apply AffineMap.ext_linear
    (linear_eq_of_native_frame u g.linear.toLinearMap h.linear.toLinearMap ht hn)
  exact hc

variable {V : Type*} (G : SimpleGraph V)
    (edgePose : ∀ u v, G.Adj u v → Pose m)

/-- Compose the actual directed edge poses; an edge `u,v` maps `v` to `u`. -/
def walkPose {u v : V} : G.Walk u v → Pose m
  | .nil => AffineEquiv.refl ℝ (Space m)
  | .cons h w => (walkPose w).trans (edgePose _ _ h)

@[simp] theorem walkPose_nil (u : V) :
    walkPose G edgePose (.nil : G.Walk u u) = AffineEquiv.refl ℝ (Space m) := rfl

/-- Every coordinate/property fixed pointwise by generator transports is
fixed pointwise by every composed walk, including arbitrary affine translations. -/
theorem walkPose_fixes_projection {Y : Type*} (π : Space m → Y)
    (hedge : ∀ u v h x, π (edgePose u v h x) = π x)
    {u v : V} (w : G.Walk u v) (x : Space m) :
    π (walkPose G edgePose w x) = π x := by
  induction w with
  | nil => rfl
  | cons h w ih =>
    change π (edgePose _ _ h (walkPose G edgePose w x)) = π x
    rw [hedge, ih]

theorem walkPose_tangents {J : Type*} (axis : V → J → Space m)
    (hedge : ∀ u v h j, (edgePose u v h).linear (axis v j) = axis u j)
    {u v : V} (w : G.Walk u v) (j : J) :
    (walkPose G edgePose w).linear (axis v j) = axis u j := by
  induction w with
  | nil => rfl
  | cons h w ih =>
    change (edgePose _ _ h).linear ((walkPose G edgePose w).linear (axis _ j)) = _
    rw [ih, hedge]

theorem walkPose_normals (normal : V → Space m)
    (hedge : ∀ u v h, (edgePose u v h).linear (normal v) = -normal u)
    {u v : V} (w : G.Walk u v) :
    (walkPose G edgePose w).linear (normal v) = (-1 : ℝ)^w.length • normal u := by
  induction w with
  | nil => simp [walkPose]
  | cons h w ih =>
    change (edgePose _ _ h).linear ((walkPose G edgePose w).linear (normal _)) = _
    rw [ih, map_smul, hedge]
    simp [SimpleGraph.Walk.length_cons, pow_succ, mul_smul]

theorem walkPose_centers (center : V → Space m)
    (hedge : ∀ u v h, edgePose u v h (center v) = center u)
    {u v : V} (w : G.Walk u v) : walkPose G edgePose w (center v) = center u := by
  induction w with
  | nil => rfl
  | cons h w ih =>
    change edgePose _ _ h (walkPose G edgePose w (center _)) = _
    rw [ih, hedge]

/-- Native determinant orientation reverses on each proper geometric edge. -/
theorem native_edge_orientation
    {u v : Site S} (g : Pose m)
    (hg : LinearMap.det g.linear.toLinearMap = 1)
    (ht : ∀ j, g.linear (siteAxis v j) = siteAxis u j)
    (hn : g.linear (outward v.1) = -outward u.1) :
    orientation v = -orientation u := by
  have hd := frame_matching_determinant g.linear.toLinearMap u v ht hn
  rw [hg, one_mul] at hd
  exact_mod_cast hd

/-- Literal opposite rank-times-determinant coefficients force the entire
candidate affine mate to be a composed odd generator transport. -/
theorem candidate_eq_odd_walk [LinearOrder (Site S)]
    (G : SimpleGraph (Site S))
    (edgePose : ∀ u v, G.Adj u v → Pose m)
    (hproper : ∀ u v h, LinearMap.det (edgePose u v h).linear.toLinearMap = 1)
    (ht : ∀ u v h j, (edgePose u v h).linear (siteAxis v j) = siteAxis u j)
    (hn : ∀ u v h, (edgePose u v h).linear (outward v.1) = -outward u.1)
    (hc : ∀ u v h, edgePose u v h (siteCenter v) = siteCenter u)
    (u v : Site S) (g : Pose m)
    (hgt : ∀ j, g.linear (siteAxis v j) = siteAxis u j)
    (hgn : g.linear (outward v.1) = -outward u.1)
    (hgc : g (siteCenter v) = siteCenter u)
    (hcoeff : value G orientation v = -value G orientation u) :
    ∃ w : G.Walk u v, Odd w.length ∧ g = walkPose G edgePose w := by
  obtain ⟨w, hw⟩ := opposite_coefficients_odd_walk G orientation orientation_sign
    (fun u v h => native_edge_orientation (edgePose u v h)
      (hproper u v h) (ht u v h) (hn u v h)) u v hcoeff
  refine ⟨w,hw,pose_eq_of_native_frame v g (walkPose G edgePose w) ?_ ?_ ?_⟩
  · intro j
    rw [hgt, walkPose_tangents G edgePose siteAxis ht w]
  · rw [hgn, walkPose_normals G edgePose (fun u => outward u.1) hn w, hw.neg_one_pow]
    simp
  · rw [hgc, walkPose_centers G edgePose siteCenter hc w]

/-- Passive pointwise identity, hence exclusion of passive translation and
frame changes, is recovered from a single matched opposite coefficient.
The candidate is initially an unrestricted affine equivalence. -/
theorem candidate_fixes_passive [LinearOrder (Site S)]
    (G : SimpleGraph (Site S))
    (edgePose : ∀ u v, G.Adj u v → Pose m)
    (hproper : ∀ u v h, LinearMap.det (edgePose u v h).linear.toLinearMap = 1)
    (ht : ∀ u v h j, (edgePose u v h).linear (siteAxis v j) = siteAxis u j)
    (hn : ∀ u v h, (edgePose u v h).linear (outward v.1) = -outward u.1)
    (hc : ∀ u v h, edgePose u v h (siteCenter v) = siteCenter u)
    {Y : Type*} (π : Space m → Y)
    (hpassive : ∀ u v h x, π (edgePose u v h x) = π x)
    (u v : Site S) (g : Pose m)
    (hgt : ∀ j, g.linear (siteAxis v j) = siteAxis u j)
    (hgn : g.linear (outward v.1) = -outward u.1)
    (hgc : g (siteCenter v) = siteCenter u)
    (hcoeff : value G orientation v = -value G orientation u) :
    ∀ x, π (g x) = π x := by
  obtain ⟨w, _, rfl⟩ := candidate_eq_odd_walk G edgePose hproper ht hn hc u v g hgt hgn hgc hcoeff
  exact walkPose_fixes_projection G edgePose π hpassive w

#print axioms linear_eq_of_native_frame
#print axioms candidate_eq_odd_walk
#print axioms candidate_fixes_passive
end
end ProductClosure.ProductGraphTransport
