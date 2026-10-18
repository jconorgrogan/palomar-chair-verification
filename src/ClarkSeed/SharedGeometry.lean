module

public import ClarkSeed.NativeFacets
public import ClarkSeed.PoseAdapter
public import ProductClosure.ProductGraphPlacements

@[expose] public section

/-! Old integer Shared facet semantics agrees with actual Euclidean centre
matching and opposite normals in the dense native finite-polycube geometry. -/
namespace ClarkSeed.SharedGeometry
open ProductClosure NativeCompiler SparseMonotiles.Contact
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m+1))}

private theorem normal_cast (f : Polycube.Facet S) :
    ((NativeFacets.toContact f).normal : ℝ) = normalSign f := by
  cases hp : f.positive <;>
    simp [NativeFacets.toContact, SparseMonotiles.Contact.Facet.normal,normalSign,sign,hp]

/-- Every old shared unit facet has exactly the intended real geometry. -/
theorem shared_iff_geometry (p : Pose (m+1)) (f g : Polycube.Facet S) :
    Shared p (NativeFacets.toContact f) (NativeFacets.toContact g) ↔
      PhysicalRegistration.NativeChair.poseIsometry (PoseAdapter.toRegistered p) (facetCenter g) =
        facetCenter f ∧
      placedNormal (PhysicalRegistration.NativeChair.poseIsometry (PoseAdapter.toRegistered p))
        (outward g) = -outward f := by
  constructor
  · rintro ⟨hc,ha,hn⟩
    constructor
    · ext i
      have hi := congrFun hc i
      have hir := congrArg (fun z : ℤ => (z : ℝ)) hi
      simp only [Pose.scaledPoint, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
        NativeFacets.centre2_cast] at hir
      rw [PoseAdapter.poseIsometry_apply]
      change (p.sign i : ℝ) * Polycube.facetCenter g (p.perm i) + (p.shift i : ℝ) =
        Polycube.facetCenter f i
      linarith
    · ext i
      rw [placedNormal_poseIsometry_apply]
      change (p.sign i : ℝ) * outward g (p.perm i) = (-outward f) i
      by_cases hi : i = f.axis
      · subst i
        have hnr := congrArg (fun z : ℤ => (z : ℝ)) hn
        simp only [Int.cast_mul, Int.cast_neg, normal_cast] at hnr
        simpa [outward, normalIndex, NativeFacets.toContact, show p.perm f.axis = g.axis from ha] using hnr
      · have hg : p.perm i ≠ g.axis := by
          rw [← (show p.perm f.axis = g.axis from ha)]
          exact p.perm.injective.ne hi
        simp [outward, normalIndex, hi, hg]
  · rintro ⟨hc,hn⟩
    have ha : p.perm f.axis = g.axis :=
      normal_index_of_facet_normals (PoseAdapter.toRegistered p) f g hn
    refine ⟨?_,ha,?_⟩
    · funext i
      apply Int.cast_injective (α := ℝ)
      simp only [Pose.scaledPoint, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
        NativeFacets.centre2_cast]
      have hi := congrArg (fun x : Space m => x i) hc
      rw [PoseAdapter.poseIsometry_apply] at hi
      change (p.sign i : ℝ) * Polycube.facetCenter g (p.perm i) + (p.shift i : ℝ) =
        Polycube.facetCenter f i at hi
      linarith
    · apply Int.cast_injective (α := ℝ)
      simp only [Int.cast_mul, Int.cast_neg, normal_cast]
      have hi := congrArg (fun x : Space m => x f.axis) hn
      rw [placedNormal_poseIsometry_apply] at hi
      change (p.sign f.axis : ℝ) * normalSign g = -normalSign f
      change (p.sign f.axis : ℝ) * outward g (p.perm f.axis) = (-outward f) f.axis at hi
      simpa [outward, normalIndex, ha] using hi


/-- Every actual dense site transport has the exact old shared-facet data. -/
theorem siteTransport_shared (p : Pose (m+1)) (u v : Site S)
    (h : SiteTransport (PhysicalRegistration.NativeChair.poseIsometry (PoseAdapter.toRegistered p)) u v) :
    Shared p (NativeFacets.toContact u.1) (NativeFacets.toContact v.1) :=
  (shared_iff_geometry p u.1 v.1).mpr
    ⟨ProductGraphPlacements.transport_facetCenter h,h.2.1⟩

/-- A shared carrier facet mates every prescribed full root frame, not only
one selected frame or a quotient of the tangent orbit. -/
theorem shared_prescribed_root (p : Pose (m+1)) (u : Site S) (g : Polycube.Facet S)
    (h : Shared p (NativeFacets.toContact u.1) (NativeFacets.toContact g)) :
    ∃ v : Site S, v.1 = g ∧
      SiteTransport (PhysicalRegistration.NativeChair.poseIsometry (PoseAdapter.toRegistered p)) u v := by
  obtain ⟨hc,hn⟩ := (shared_iff_geometry p u.1 g).mp h
  exact exists_siteTransport_prescribed_root (PoseAdapter.toRegistered p) u g hc hn

/-- Old shared facets therefore supply genuine native matched-site witnesses. -/
theorem shared_exists_siteTransport (p : Pose (m+1)) (f g : Polycube.Facet S)
    (h : Shared p (NativeFacets.toContact f) (NativeFacets.toContact g)) :
    ∃ u v : Site S, u.1 = f ∧ v.1 = g ∧
      SiteTransport (PhysicalRegistration.NativeChair.poseIsometry (PoseAdapter.toRegistered p)) u v := by
  let u : Site S := (f,Equiv.refl _,fun _ => true)
  obtain ⟨v,hv,ht⟩ := shared_prescribed_root p u g h
  exact ⟨u,v,rfl,hv,ht⟩

end
end ClarkSeed.SharedGeometry
