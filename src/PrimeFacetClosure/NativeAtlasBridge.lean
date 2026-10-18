module

public import PrimeFacetClosure.NativeFreeOrbit
public import PrimeFacetClosure.HoleAtlasBridge

@[expose] public section

/-! Literal native facet centers and full-orbit sites feed the integer
mean-obstruction and hole atlas bridges. -/
namespace PhysicalRegistration.NativeChair
noncomputable section
open RegisteredPrime.PrimeFacetClosure

/-- Integer doubled coordinates of the literal native carrier facet center. -/
def facetCenter2 {m : ℕ} : Facet m → RegisteredPrime.Cell (m+1)
  | .inl (A,j) => outerFacetCenter2 A.val j
  | .inr k => innerFacetCenter2 k

@[simp] theorem cast_facetCenter2 {m : ℕ} (f : Facet m) (i : Fin (m+1)) :
    (facetCenter2 f i : ℝ) = 2 * facetCenter f i := by
  cases f with
  | inl a =>
    rcases a with ⟨A,j⟩
    by_cases hij : i = j
    · subst i
      cases hA : A.val j <;>
        norm_num [facetCenter2, outerFacetCenter2, facetCenter, RegisteredPrime.bit, hA]
    · cases hA : A.val i <;>
        norm_num [facetCenter2, outerFacetCenter2, facetCenter, RegisteredPrime.bit, bit, hij, hA]
  | inr k =>
    by_cases hik : i = k <;> norm_num [facetCenter2, innerFacetCenter2, facetCenter, hik]

@[simp] theorem cast_mapPoint2_facetCenter2 {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (f : Facet m) (i : Fin (m+1)) :
    (mapPoint2 q (facetCenter2 f) i : ℝ) = 2 * poseIsometry q (facetCenter f) i := by
  simp only [mapPoint2, RegisteredPrime.RegisteredFrame.linear, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat, cast_facetCenter2, poseIsometry_apply]
  ring

/-- Exact equivalence, not just a compatibility assertion, between the
integer facet-center equations and the literal Euclidean native geometry. -/
theorem mapPoint2_facetCenter2_iff {m : ℕ} (q : RegisteredPrime.Pose (m+1))
    (f g : Facet m) :
    mapPoint2 q (facetCenter2 g) = facetCenter2 f ↔
      poseIsometry q (facetCenter g) = facetCenter f := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun z : RegisteredPrime.Cell (m+1) => (z i : ℝ)) h
    rw [cast_mapPoint2_facetCenter2, cast_facetCenter2] at hi
    linarith
  · intro h
    funext i
    apply Int.cast_injective (α := ℝ)
    rw [cast_mapPoint2_facetCenter2, cast_facetCenter2, h]

/-- A proper arithmetic role is an actual occupied native cell, including
empty roles; no nonemptiness restriction is imposed. -/
def nativeCellOfMask {m : ℕ} (A : RegisteredPrime.Mask (m+1))
    (hA : RegisteredPrime.Proper A) : Cell m :=
  ⟨A, by intro h; obtain ⟨i, hi⟩ := hA; have hh := congrFun h i; simp [hi] at hh⟩

/-- Every available shared outer unit cell at a registered wall supplies a
literal matched full-orbit native-site pair on precisely those two facets. -/
theorem exists_siteTransport_outer_shared_cell {m : ℕ}
    (q : RegisteredPrime.Pose (m+1)) (A B : Cell m) (j : Fin (m+1)) (side : Bool)
    (hbox : RegisteredPrime.boxLower q = RegisteredPrime.wallBox j side)
    (hs : A.val j = side)
    (hcell : q.cell (cellIndex B) = RegisteredPrime.exterior A.val j) :
    ∃ U V : Frame m, SiteTransport (poseIsometry q)
      (.inl (A,j), U) (.inl (B,q.frame.perm j), V) := by
  have hcell' : q.cell (fun i => RegisteredPrime.bit (B.val i)) =
      RegisteredPrime.exterior A.val j := by simpa only [cellIndex_eq_registered_bits] using hcell
  have hm := (wall_shared_cell_iff q j side hbox A.val B.val hs).mp hcell'
  have hc : poseIsometry q (facetCenter (.inl (B,q.frame.perm j))) = facetCenter (.inl (A,j)) :=
    (mapPoint2_facetCenter2_iff q _ _).mp
      (outer_centers_of_wall_shared_cell q j side hbox A.val B.val hs hcell')
  have hn : placedNormal (poseIsometry q) (outward (.inl (B,q.frame.perm j))) =
      -outward (.inl (A,j)) := by
    ext i
    rw [placedNormal_poseIsometry_apply]
    by_cases hij : i = j
    · subst i
      have h := hm j
      cases ha : A.val j <;> cases hd : q.frame.negative j <;>
        cases hb : B.val (q.frame.perm j) <;>
        simp [wallToggle, ha, hd, hb, outward, normalIndex, normalSign,
          RegisteredPrime.RegisteredFrame.sign, sign] at h ⊢
    · have hpi : q.frame.perm i ≠ q.frame.perm j := by
        intro he
        have hh := congrArg q.frame.inverse he
        exact hij (by simpa only [q.frame.left_inverse] using hh)
      simp [outward, normalIndex, normalSign, hpi, hij]
  obtain ⟨u, v, hu, hv, ht⟩ := exists_siteTransport_of_facet_match q _ _ hc hn
  exact ⟨u.2, v.2, by simpa only [← hu, ← hv] using ht⟩

/-- Actual matched native sites with outer/inner facets give an incoming
atlas contact once the path calculation identifies the star-gauge frame. -/
theorem native_incoming_arithmetic_atlas {m : ℕ}
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (q : RegisteredPrime.Pose (m+1)) (A : Cell m) (j k : Fin (m+1)) (U V : Frame m)
    (ht : SiteTransport (poseIsometry q) (.inl (A,j), U) (.inr k, V))
    (hf : q.frame = (RegisteredPrime.arithmeticChild (minusParameters (m+1) hp hmod)
      (.outer A.val (nativeCell_proper A))).frame) :
    RegisteredPrime.ArithmeticAtlasContact (minusParameters (m+1) hp hmod) q := by
  let P := minusParameters (m+1) hp hmod
  have hi := ht.normal_index
  change q.frame.perm j = k at hi
  have hc := (mapPoint2_facetCenter2_iff q (.inl (A,j)) (.inr k)).mpr ht.facet_center
  change mapPoint2 q (innerFacetCenter2 k) = outerFacetCenter2 A.val j at hc
  rw [← hi, hf] at hc
  exact incoming_facet_atlas_of_outer_frame P rfl q A.val (nativeCell_proper A) j hf hc

/-- The reverse native hole pairing yields the exact inverse-incoming atlas
contact. Only actual full frame and facet-center transport are used. -/
theorem native_outgoing_arithmetic_atlas {m : ℕ}
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (q : RegisteredPrime.Pose (m+1)) (A : Cell m) (k j : Fin (m+1)) (U V : Frame m)
    (ht : SiteTransport (poseIsometry q) (.inr k, U) (.inl (A,j), V))
    (hf : q.inv.frame = (RegisteredPrime.arithmeticChild (minusParameters (m+1) hp hmod)
      (.outer A.val (nativeCell_proper A))).frame) :
    RegisteredPrime.ArithmeticAtlasContact (minusParameters (m+1) hp hmod) q := by
  let P := minusParameters (m+1) hp hmod
  have hi := ht.normal_index
  change q.frame.perm k = j at hi
  have hik : q.frame.inverse j = k := by rw [← hi, q.frame.left_inverse]
  have hc := (mapPoint2_facetCenter2_iff q (.inr k) (.inl (A,j))).mpr ht.facet_center
  change mapPoint2 q (outerFacetCenter2 A.val j) = innerFacetCenter2 k at hc
  have hfperm := congrArg (fun H : RegisteredPrime.RegisteredFrame (m+1) => H.perm j) hf
  change q.frame.inverse j = _ at hfperm
  rw [← hik, hfperm] at hc
  exact inverse_incoming_facet_atlas_of_outer_frame P rfl q A.val (nativeCell_proper A) j hf hc

/-- A native inner/inner matched pair with the odd bridge is incompatible
with actual registered carrier nonoverlap. -/
theorem native_inner_bridge_not_disjoint {m : ℕ}
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (q : RegisteredPrime.Pose (m+1)) (F : RegisteredPrime.RegisteredFrame (m+1))
    (j k : Fin (m+1)) (U V : Frame m)
    (ht : SiteTransport (poseIsometry q) (.inr j, U) (.inr k, V))
    (hf : q.frame = bridge F j) : ¬ RegisteredPrime.Disjoint (RegisteredPrime.identityPose (m+1)) q := by
  have hi := ht.normal_index
  change q.frame.perm j = k at hi
  have hc := (mapPoint2_facetCenter2_iff q (.inr j) (.inr k)).mpr ht.facet_center
  change mapPoint2 q (innerFacetCenter2 k) = innerFacetCenter2 j at hc
  rw [← hi, hf] at hc
  exact inner_bridge_not_disjoint (minusParameters (m+1) hp hmod) q F j hf hc

/-- Concrete outer/outer native frame equations imply atlas membership.
Every shared arithmetic role is explicitly upgraded to an available full-orbit
native-site pair, so the universal mean test has no missing-facet premise. -/
theorem native_outer_arithmetic_atlas {m : ℕ}
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (q : RegisteredPrime.Pose (m+1)) (F : RegisteredPrime.RegisteredFrame (m+1))
    (hF : F.AffineIndex)
    (hF0 : F.perm (RegisteredPrime.zeroIndex (minusParameters (m+1) hp hmod)) =
      RegisteredPrime.zeroIndex (minusParameters (m+1) hp hmod))
    (hframes : ∀ (A B : Cell m) (j k : Fin (m+1)) (U V : Frame m),
      SiteTransport (poseIsometry q) (.inl (A,j),U) (.inl (B,k),V) →
      (((RegisteredPrime.arithmeticChild (minusParameters (m+1) hp hmod)
        (.outer A.val (nativeCell_proper A))).frame.inv.comp q.frame).comp
        (RegisteredPrime.arithmeticChild (minusParameters (m+1) hp hmod)
          (.outer B.val (nativeCell_proper B))).frame) =
        bridge F ((RegisteredPrime.arithmeticChild (minusParameters (m+1) hp hmod)
          (.outer A.val (nativeCell_proper A))).frame.perm j))
    (A B : Cell m) (j k : Fin (m+1)) (U V : Frame m)
    (ht : SiteTransport (poseIsometry q) (.inl (A,j),U) (.inl (B,k),V)) :
    RegisteredPrime.ArithmeticAtlasContact (minusParameters (m+1) hp hmod) q := by
  let P := minusParameters (m+1) hp hmod
  have hf := hframes A B j k U V ht
  have hc : q.cell (cellIndex B) = RegisteredPrime.exterior A.val j := by
    simpa only [facetInsideCell, facetOutsideIndex_outer] using ht.registered_cell
  have hc' : q.cell (fun i => RegisteredPrime.bit (B.val i)) =
      RegisteredPrime.exterior A.val j := by simpa only [cellIndex_eq_registered_bits] using hc
  have hb := outer_frame_transport_wall_box P q A.val B.val
    (nativeCell_proper A) (nativeCell_proper B) j F hc' hf
  apply wall_arithmetic_atlas_of_frame_transport P q j (A.val j) F hb hF hF0
  intro C D hC hD hs hcell
  let c := nativeCellOfMask C hC
  let d := nativeCellOfMask D hD
  have hcell' : q.cell (cellIndex d) = RegisteredPrime.exterior c.val j := by
    exact hcell
  obtain ⟨X, Y, hxy⟩ := exists_siteTransport_outer_shared_cell q c d j (A.val j) hb hs hcell'
  exact ⟨(RegisteredPrime.arithmeticChild P (.outer C hC)).frame.perm j,
    hframes c d j (q.frame.perm j) X Y hxy⟩

#print axioms mapPoint2_facetCenter2_iff
#print axioms exists_siteTransport_outer_shared_cell
#print axioms native_incoming_arithmetic_atlas
#print axioms native_outgoing_arithmetic_atlas
#print axioms native_inner_bridge_not_disjoint
#print axioms native_outer_arithmetic_atlas
end
end PhysicalRegistration.NativeChair
