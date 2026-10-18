module

public import PhysicalRegistration.PoseRealization
public import ProductClosure.NativeTubeSeparation

@[expose] public section

/-! Literal coordinate enclosures for arbitrary registered placements of
native closed tubes. Overlapping tubes must lie on the same placed unit facet.
No tiling, registered-world or contact-language hypothesis is required. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration PhysicalRegistration.NativeChair
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

def registeredFacetAxis  (q : RegisteredPrime.Pose (m+1))
    (f : Facet S) : Fin (m+1) := q.frame.inverse (normalIndex f)

def registeredFacetPlane  (q : RegisteredPrime.Pose (m+1))
    (f : Facet S) : ℤ :=
  q.frame.sign (registeredFacetAxis q f) * facetPlane f + q.anchor (registeredFacetAxis q f)

def registeredFacetCell  (q : RegisteredPrime.Pose (m+1))
    (f : Facet S) (k : Fin (m+1)) : ℤ :=
  q.anchor k + q.frame.sign k * facetCellCoordinate f (q.frame.perm k) -
    RegisteredPrime.bit (q.frame.negative k)

def registeredSiteOffset  (q : RegisteredPrime.Pose (m+1))
    (u : Site S) (k : Fin (m+1)) : ℝ :=
  (q.frame.sign k : ℝ) * siteOffset u (q.frame.perm k)

theorem registeredFacetAxis_perm  (q : RegisteredPrime.Pose (m+1)) (f : Facet S) :
    q.frame.perm (registeredFacetAxis q f) = normalIndex f := q.frame.right_inverse _

theorem registeredFacetAxis_ne_iff  (q : RegisteredPrime.Pose (m+1))
    (f : Facet S) (k : Fin (m+1)) :
    k ≠ registeredFacetAxis q f ↔ q.frame.perm k ≠ normalIndex f := by
  constructor
  · intro h he
    have hi := congrArg q.frame.inverse he
    exact h (by simpa only [q.frame.left_inverse, registeredFacetAxis] using hi)
  · intro h he
    apply h
    rw [he, registeredFacetAxis_perm]

theorem registeredSiteOffset_bound  (q : RegisteredPrime.Pose (m+1))
    (u : Site S) (k : Fin (m+1)) : |registeredSiteOffset q u k| < 1 / 4 := by
  have h := siteOffset_coordinate_bound u (q.frame.perm k)
  cases hn : q.frame.negative k <;>
    simpa [registeredSiteOffset, RegisteredPrime.RegisteredFrame.sign, hn] using h

theorem registered_facetCenter_normal  (q : RegisteredPrime.Pose (m+1))
    (f : Facet S) :
    poseIsometry q (facetCenter f) (registeredFacetAxis q f) = (registeredFacetPlane q f : ℝ) := by
  rw [poseIsometry_apply, registeredFacetAxis_perm, facetCenter_normal]
  simp [registeredFacetPlane]

theorem registered_facetCenter_tangent  (q : RegisteredPrime.Pose (m+1))
    (f : Facet S) (k : Fin (m+1)) (hk : k ≠ registeredFacetAxis q f) :
    poseIsometry q (facetCenter f) k = (registeredFacetCell q f k : ℝ) + 1 / 2 := by
  rw [poseIsometry_apply, facetCenter_tangent f _ ((registeredFacetAxis_ne_iff q f k).mp hk)]
  cases hn : q.frame.negative k <;>
    simp [registeredFacetCell, RegisteredPrime.RegisteredFrame.sign, RegisteredPrime.bit, hn] <;> ring

theorem registered_siteCenter_normal  (q : RegisteredPrime.Pose (m+1))
    (u : Site S) :
    poseIsometry q (siteCenter u) (registeredFacetAxis q u.1) = (registeredFacetPlane q u.1 : ℝ) := by
  rw [poseIsometry_apply, registeredFacetAxis_perm, siteCenter_normal]
  simp [registeredFacetPlane]

theorem registered_siteCenter_tangent  (q : RegisteredPrime.Pose (m+1))
    (u : Site S) (k : Fin (m+1)) (hk : k ≠ registeredFacetAxis q u.1) :
    poseIsometry q (siteCenter u) k =
      (registeredFacetCell q u.1 k : ℝ) + 1 / 2 + registeredSiteOffset q u k := by
  rw [poseIsometry_apply, siteCenter_tangent u _ ((registeredFacetAxis_ne_iff q u.1 k).mp hk)]
  cases hn : q.frame.negative k <;>
    simp [registeredFacetCell, registeredSiteOffset, RegisteredPrime.RegisteredFrame.sign,
      RegisteredPrime.bit, hn] <;> ring

/-- Signed row maps preserve absolute coordinate differences. -/
theorem poseIsometry_coordinate_distance  (q : RegisteredPrime.Pose (m+1))
    (x y : Space m) (k : Fin (m+1)) :
    |poseIsometry q x k - poseIsometry q y k| = |x (q.frame.perm k) - y (q.frame.perm k)| := by
  rw [poseIsometry_apply, poseIsometry_apply]
  cases hn : q.frame.negative k <;>
    simp only [RegisteredPrime.RegisteredFrame.sign, hn, Bool.false_eq_true, ite_false,
      ite_true, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul, add_sub_add_right_eq_sub]
  rw [show -x (q.frame.perm k) - -y (q.frame.perm k) =
    -(x (q.frame.perm k) - y (q.frame.perm k)) by ring, abs_neg]

/-- Every point of a placed tube lies in the correctly permuted coordinate
enclosure at the unchanged construction widths. -/
theorem registered_tube_coordinate_enclosure {J : ℕ}
    (q : RegisteredPrime.Pose (m+1)) (u : Site S) {x : Space m}
    (hx : x ∈ poseIsometry q '' closedTube J u) :
    (fun k => x k) ∈ coordinateTube (registeredFacetAxis q u.1)
      (fun k => poseIsometry q (siteCenter u) k) (eta m) (rho m) := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hh := closedTube_mem_coordinateTube u y hy
  constructor
  · rw [poseIsometry_coordinate_distance, registeredFacetAxis_perm]
    exact hh.1
  · intro k hk
    rw [poseIsometry_coordinate_distance]
    exact hh.2 _ ((registeredFacetAxis_ne_iff q u.1 k).mp hk)

end
end ProductClosure.NativeCompiler
