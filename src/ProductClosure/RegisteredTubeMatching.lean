module

public import ProductClosure.RegisteredTubeSeparation
public import ProductClosure.MaterialCovariance
public import ProductClosure.NativePrescribedOrbit

@[expose] public section

/-! An intersecting pair of actual native tubes with opposite normals has
exact full-site transport. This uses the full unquotiented tangent orbit and
strict native tube separation, with no assumed component or matching label. -/
namespace ProductClosure.NativeCompiler
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}
open Set RegisteredPrime PhysicalRegistration.NativeChair

 theorem siteTransport_of_tube_intersection_opposite {J : ℕ} (hm : 2 ≤ m)
    (q : Pose (m+1)) (u v : Site S)
    (hx : (closedTube J u ∩ poseIsometry q '' closedTube J v).Nonempty)
    (hn : placedNormal (poseIsometry q) (outward v.1) = -outward u.1) :
    SiteTransport (poseIsometry q) u v := by
  have hc := registered_closedTube_intersection_facetCenter hm q u v hx
  obtain ⟨w,_,hw⟩ := exists_siteTransport_prescribed_root q u v.1 hc hn
  have hvw : v=w := by
    by_contra hne
    obtain ⟨x,hxu,y,hy,hxy⟩ := hx
    have hyw : y ∈ closedTube J w := (hw.closedTube_iff J y).mp (hxy ▸ hxu)
    exact Set.disjoint_left.mp (closedTube_pairwise_disjoint hm hne) hy hyw
  rwa [←hvw] at hw

 theorem registered_tubes_disjoint_or_matched {J : ℕ} (hm : 2 ≤ m)
    (q : Pose (m+1)) (u v : Site S)
    (hn : (closedTube J u ∩ poseIsometry q '' closedTube J v).Nonempty →
      placedNormal (poseIsometry q) (outward v.1) = -outward u.1) :
    _root_.Disjoint (closedTube J u) (poseIsometry q '' closedTube J v) ∨
      SiteTransport (poseIsometry q) u v := by
  by_cases hx : (closedTube J u ∩ poseIsometry q '' closedTube J v).Nonempty
  · exact Or.inr (siteTransport_of_tube_intersection_opposite hm q u v hx (hn hx))
  · left
    apply Set.disjoint_left.mpr
    intro x hu hv
    exact hx ⟨x,hu,hv⟩

#print axioms siteTransport_of_tube_intersection_opposite
#print axioms registered_tubes_disjoint_or_matched
end
end ProductClosure.NativeCompiler
