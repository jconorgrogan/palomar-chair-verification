module

public import PhysicalRegistration.PoseRealization
public import PhysicalRegistration.NativeGraphCoefficients
public import PrimeFacetClosure.Reflection
public import PrimeFacetClosure.Parameters

@[expose] public section

/-! Literal native facet transport in the existing registered row convention.
These lemmas extract full unit-cell adjacency and anchor parity from actual
site-frame/center matching. No facet closure or atlas law is assumed. -/
namespace PhysicalRegistration.NativeChair
noncomputable section
open RegisteredPrime.PrimeFacetClosure

 theorem nativeCell_proper {m : ℕ} (A : Cell m) : RegisteredPrime.Proper A.val := by
  by_contra h
  apply A.property
  funext i
  have hi : A.val i ≠ false := fun he => h ⟨i, he⟩
  cases he : A.val i <;> simp_all

 theorem cellIndex_eq_registered_bits {m : ℕ} (A : Cell m) :
    cellIndex A = fun i => RegisteredPrime.bit (A.val i) := by
  funext i
  rfl

 theorem facetOutsideIndex_outer {m : ℕ} (A : Cell m) (j : Fin (m+1)) :
    facetOutsideIndex (.inl (A,j)) = RegisteredPrime.exterior A.val j := by
  funext i
  by_cases hij : i=j
  · subst i
    cases ha : A.val j <;> simp [facetOutsideIndex,facetInsideCell,normalIndex,
      facetPositive,latticeStep,cellIndex,RegisteredPrime.exterior,RegisteredPrime.bit,ha]
  · cases ha : A.val i <;> simp [facetOutsideIndex,facetInsideCell,normalIndex,facetPositive,latticeStep,
      cellIndex,RegisteredPrime.exterior,RegisteredPrime.bit,hij,ha]

 theorem facetOutsideIndex_inner {m : ℕ} (j : Fin (m+1)) :
    facetOutsideIndex (.inr j) = fun _ => 1 := by
  funext i
  by_cases hij : i=j <;> simp [facetOutsideIndex,facetInsideCell,normalIndex,
    facetPositive,latticeStep,cellIndex,hij]

 theorem placedNormal_poseIsometry_apply {m : ℕ}
    (q : RegisteredPrime.Pose (m+1)) (x : Space m) (i : Fin (m+1)) :
    placedNormal (poseIsometry q) x i = (q.frame.sign i : ℝ) * x (q.frame.perm i) := by
  have h := congrArg (fun y : Space m => y i) (placedNormal_eq_sub_zero (poseIsometry q) x)
  simpa [poseIsometry_apply] using h

 theorem SiteTransport.facet_center {m : ℕ} {e : Space m ≃ᵢ Space m}
    {u v : Site m} (h : SiteTransport e u v) : e (facetCenter v.1) = facetCenter u.1 := by
  have hh := relativePlacement_facetCenter u v (IsometryEquiv.refl (Space m)) e
    (by simpa only [placedNormal_refl] using h.1) (by exact h.2.2.symm)
  exact hh

 theorem SiteTransport.registered_cell {m : ℕ} {q : RegisteredPrime.Pose (m+1)}
    {u v : Site m} (h : SiteTransport (poseIsometry q) u v) :
    q.cell (cellIndex (facetInsideCell v.1)) = facetOutsideIndex u.1 := by
  apply latticeCenter_injective
  have hh := matched_companion_cellCenter u v (IsometryEquiv.refl (Space m)) (poseIsometry q)
    (by simpa only [placedNormal_refl] using h.1)
    (by simpa only [placedNormal_refl] using h.2.1) (by exact h.2.2.symm)
  have hm := (poseIsometry_realizes q).map_latticeCenter (cellIndex (facetInsideCell v.1))
  rw [latticeCenter_cellIndex] at hm
  exact hm.symm.trans hh

 theorem SiteTransport.normal_index {m : ℕ} {q : RegisteredPrime.Pose (m+1)}
    {u v : Site m} (h : SiteTransport (poseIsometry q) u v) :
    q.frame.perm (normalIndex u.1) = normalIndex v.1 := by
  by_contra hi
  have hh := congrArg (fun x : Space m => x (normalIndex u.1)) h.2.1
  rw [placedNormal_poseIsometry_apply] at hh
  have hn : normalSign u.1 ≠ 0 := by
    intro hz
    have ha := abs_normalSign u.1
    rw [hz, abs_zero] at ha
    norm_num at ha
  apply hn
  simpa [outward, PiLp.smul_apply, hi] using hh

 def isOuter {m : ℕ} : Facet m → Bool
  | .inl _ => true
  | .inr _ => false

 theorem facetCenter_normal_plane {m : ℕ} (f : Facet m) :
    facetCenter f (normalIndex f) = (facetPlane f : ℝ) := by
  cases f with
  | inl a => cases h : a.1.val a.2 <;> simp [facetCenter,normalIndex,facetPlane,h]
  | inr j => simp [facetCenter,normalIndex,facetPlane]

 theorem SiteTransport.anchor_normal_plane {m : ℕ} {q : RegisteredPrime.Pose (m+1)}
    {u v : Site m} (h : SiteTransport (poseIsometry q) u v) :
    q.anchor (normalIndex u.1) = facetPlane u.1 -
      q.frame.sign (normalIndex u.1) * facetPlane v.1 := by
  have hh := congrArg (fun x : Space m => x (normalIndex u.1)) h.facet_center
  rw [poseIsometry_apply, h.normal_index, facetCenter_normal_plane,
    facetCenter_normal_plane] at hh
  have he : (q.anchor (normalIndex u.1) : ℝ) = (facetPlane u.1 : ℝ) -
      (q.frame.sign (normalIndex u.1) : ℝ) * (facetPlane v.1 : ℝ) := by linarith
  exact_mod_cast he

/-- The parity distinguishes the two actual facet types and uses no prior
parity restriction on the candidate pose. -/
 theorem SiteTransport.anchor_normal_parity {m : ℕ} {q : RegisteredPrime.Pose (m+1)}
    {u v : Site m} (h : SiteTransport (poseIsometry q) u v) :
    q.anchor (normalIndex u.1) % 2 = if isOuter u.1 = isOuter v.1 then 0 else 1 := by
  rw [h.anchor_normal_plane]
  generalize hd : q.frame.sign (normalIndex u.1) = d
  have hs : d = 1 ∨ d = -1 := by
    rw [← hd]
    unfold RegisteredPrime.RegisteredFrame.sign
    split <;> simp
  rcases hs with rfl | rfl <;> cases hu : u.1 with
  | inl a =>
    cases hv : v.1 with
    | inl b =>
      cases ha : a.1.val a.2 <;> cases hb : b.1.val b.2 <;>
        simp [facetPlane,isOuter,hu,hv,ha,hb,RegisteredPrime.RegisteredFrame.sign,hd]
    | inr k =>
      cases ha : a.1.val a.2 <;>
        simp [facetPlane,isOuter,hu,hv,ha,RegisteredPrime.RegisteredFrame.sign,hd]
  | inr j =>
    cases hv : v.1 with
    | inl b =>
      cases hb : b.1.val b.2 <;>
        simp [facetPlane,isOuter,hu,hv,hb,RegisteredPrime.RegisteredFrame.sign,hd]
    | inr k =>
      simp [facetPlane,isOuter,hu,hv,RegisteredPrime.RegisteredFrame.sign,hd]

#print axioms SiteTransport.registered_cell
#print axioms SiteTransport.normal_index
#print axioms SiteTransport.anchor_normal_parity
end
end PhysicalRegistration.NativeChair
