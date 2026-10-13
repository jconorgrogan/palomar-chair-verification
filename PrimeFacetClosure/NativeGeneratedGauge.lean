module

public import PrimeFacetClosure.NativeFacetGeometry
public import PrimeFacetClosure.HoleAtlasBridge
public import PrimeFacetClosure.RegisteredStarTransport

@[expose] public section

/-! Concrete star-gauge classification of every actual generated native
site edge for μ=1,g=-1. The proof uses generated refinement, literal facet
centers and registered geometry, without an assumed E catalogue. -/
namespace PhysicalRegistration.NativeChair
noncomputable section
open RegisteredPrime RegisteredPrime.PrimeFacetClosure
open RegisteredPrime.PrimeFacetClosure.StarHolonomy

 theorem poseIsometry_inverse {m : ℕ} (q : Pose (m+1)) :
    poseIsometry q.inv = (poseIsometry q).symm := by
  apply IsometryEquiv.ext
  intro x
  apply (poseIsometry q).injective
  have hh := congrArg (fun e : Space m ≃ᵢ Space m => e x) (poseIsometry_comp q q.inv)
  rw [Pose.comp_inv, poseIsometry_identity] at hh
  rw [IsometryEquiv.apply_symm_apply]
  exact hh.symm

 theorem SiteTransport.registered_inverse {m : ℕ} {q : Pose (m+1)}
    {u v : Site m} (h : SiteTransport (poseIsometry q) u v) :
    SiteTransport (poseIsometry q.inv) v u := by
  rw [poseIsometry_inverse]
  exact NativeWalkTransport.siteTransport_symm h

 theorem generated_root_face_contact (P : Parameters) (q : Pose P.p)
    (hq : GeneratedContact P q) : FaceContact (identityPose P.p) q := by
  obtain ⟨n,a,b,ha,hb,hc,he⟩ := hq
  have h := a.inv.face_contact a b hc
  rw [Pose.inv_comp] at h
  change FaceContact (identityPose P.p) (a.relative b) at h
  rwa [he.eq] at h

 theorem generated_all_parity_of_index (P : Parameters) (q : Pose P.p)
    (hq : GeneratedContact P q) (j : Fin P.p) (r : ℤ) (hj : q.anchor j % 2=r) :
    ∀ i, q.anchor i % 2=r := by
  obtain ⟨b,hb⟩ := generated_contact_constant_parity P q hq
  exact fun i => (hb i).trans ((hb j).symm.trans hj)

 theorem anchor_parity_box {p : ℕ} (q : Pose p) (r : ℤ)
    (h : ∀ i, q.anchor i % 2=r) : ∀ i, boxLower q i % 2=r := by
  intro i
  have hi := h i
  cases hn : q.frame.negative i <;> simp [boxLower,RegisteredPrime.bit,hn] <;> omega

 theorem outgoing_seed_odd (P : Parameters) (q : Pose P.p) (hq : OutgoingSeed P q) :
    ∀ i, q.anchor i % 2=1 := by
  obtain ⟨A,hA,rfl⟩ := hq
  intro i
  unfold outgoingSeed
  rw [relative_anchor,child_outer_anchor,child_central_anchor]
  simp only [RegisteredFrame.sign,child_outer_negative]
  cases A ((arithmeticChild P (.outer A hA)).frame.inverse i) <;> norm_num

/-- A literal root outer facet mated with an inner facet forces exactly its
prescribed incoming pose. Odd parity and carrier nonoverlap do the geometry. -/
 theorem generated_outer_inner_pose {m : ℕ} (hp : Uniform.IsPrime (m+1))
    (hmod : (m+1)%4=3) (q : Pose (m+1))
    (hq : GeneratedContact (minusParameters (m+1) hp hmod) q)
    (A : NativeChair.Cell m) (j k : Fin (m+1)) (U V : Frame m)
    (ht : SiteTransport (poseIsometry q) ((.inl (A,j)),U) ((.inr k),V)) :
    q = incomingPose (minusParameters (m+1) hp hmod) A.val (nativeCell_proper A) := by
  let P := minusParameters (m+1) hp hmod
  have hc := ht.registered_cell
  rw [facetOutsideIndex_outer] at hc
  have ho : Occupies q (exterior A.val j) :=
    ⟨cellIndex (facetInsideCell (.inr k)), cellIndex_unitChairCell _, hc⟩
  have hpj : q.anchor j % 2=1 := by
    simpa [isOuter,normalIndex] using ht.anchor_normal_parity
  have hpall := anchor_parity_box q 1 (generated_all_parity_of_index P q hq j 1 hpj)
  have hn : ¬ Occupies q (fun i => RegisteredPrime.bit (A.val i)) := by
    intro hx
    exact (generated_root_face_contact P q hq).1 _ ⟨root_owns_role A.val (nativeCell_proper A),hx⟩
  exact (incoming_frame_property P q hq A.val (nativeCell_proper A)
    ⟨odd_exterior_box q A.val j ho hpall,odd_exterior_hole q A.val j ho hpall hn⟩).eq

/-- The concrete gauge and star label are determined by the native facet. -/
def facetStarGauge {m : ℕ} (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3) :
    Facet m → RegisteredFrame (m+1)
  | .inl (A,_) => (arithmeticChild (minusParameters (m+1) hp hmod)
      (.outer A.val (nativeCell_proper A))).frame
  | .inr _ => oneFrame (m+1)

def facetStarLabel {m : ℕ} (hp : Uniform.IsPrime (m+1)) (hmod : (m+1)%4=3) :
    Facet m → Fin (m+1)
  | .inl (A,j) => (facetStarGauge hp hmod (.inl (A,j))).perm j
  | .inr k => k

 theorem generated_outer_outer_gauge {m : ℕ} (hp : Uniform.IsPrime (m+1))
    (hmod : (m+1)%4=3) (q : Pose (m+1))
    (hq : GeneratedContact (minusParameters (m+1) hp hmod) q)
    (A B : NativeChair.Cell m) (j k : Fin (m+1)) (U V : Frame m)
    (ht : SiteTransport (poseIsometry q) ((.inl (A,j)),U) ((.inl (B,k)),V)) :
    gauged (facetStarGauge hp hmod (.inl (A,j))) q.frame
      (facetStarGauge hp hmod (.inl (B,k))) =
      bridge (reflectionFrame (minusParameters (m+1) hp hmod))
        (facetStarLabel hp hmod (.inl (A,j))) := by
  let P := minusParameters (m+1) hp hmod
  have hc : q.cell (fun i => RegisteredPrime.bit (B.val i)) = exterior A.val j := by
    simpa only [facetInsideCell, cellIndex_eq_registered_bits, facetOutsideIndex_outer]
      using ht.registered_cell
  have ho : Occupies q (exterior A.val j) :=
    ⟨cellIndex B, cellIndex_unitChairCell B, by simpa only [cellIndex_eq_registered_bits] using hc⟩
  have hpj : q.anchor j % 2=0 := by
    simpa [isOuter,normalIndex] using ht.anchor_normal_parity
  have hpall := anchor_parity_box q 0 (generated_all_parity_of_index P q hq j 0 hpj)
  have hb := even_exterior_box q A.val j ho hpall
  have hab := (wall_shared_cell_iff q j (A.val j) hb A.val B.val rfl).mp hc
  have hh := generated_wall_gauge_bridge P rfl rfl q hq j (A.val j) hb
    A.val B.val (nativeCell_proper A) (nativeCell_proper B) rfl hab
  change gauged _ _ _ = _
  change ((arithmeticChild P (.outer A.val (nativeCell_proper A))).frame.inv.comp
    (q.frame.comp (arithmeticChild P (.outer B.val (nativeCell_proper B))).frame)) = _ at hh
  change (((arithmeticChild P (.outer A.val (nativeCell_proper A))).frame.inv.comp q.frame).comp
    (arithmeticChild P (.outer B.val (nativeCell_proper B))).frame) = _
  exact (frame_comp_assoc _ _ _).trans hh

 theorem generated_inner_inner_impossible {m : ℕ} (hp : Uniform.IsPrime (m+1))
    (hmod : (m+1)%4=3) (q : Pose (m+1))
    (hq : GeneratedContact (minusParameters (m+1) hp hmod) q)
    (j k : Fin (m+1)) (U V : Frame m)
    (ht : SiteTransport (poseIsometry q) ((.inr j),U) ((.inr k),V)) : False := by
  let P := minusParameters (m+1) hp hmod
  have hc := ht.registered_cell
  rw [facetOutsideIndex_inner] at hc
  have ho : Occupies q (fun _ => 1) :=
    ⟨cellIndex (facetInsideCell (.inr k)),cellIndex_unitChairCell _,hc⟩
  have hod := outgoing_seed_odd P q (generated_outgoing_seed P q hq ho) j
  have hev : q.anchor j % 2=0 := by
    simpa [isOuter,normalIndex] using ht.anchor_normal_parity
  omega

/-- Every generated contact, at every actual full native site mating, has
exactly one of the prescribed star transports. No catalogue is assumed. -/
 theorem generated_native_classification {m : ℕ} (hp : Uniform.IsPrime (m+1))
    (hmod : (m+1)%4=3) (q : Pose (m+1))
    (hq : GeneratedContact (minusParameters (m+1) hp hmod) q)
    (u v : Site m) (ht : SiteTransport (poseIsometry q) u v) :
    (isOuter v.1 = !isOuter u.1 ∧ facetStarLabel hp hmod v.1 = facetStarLabel hp hmod u.1 ∧
      gauged (facetStarGauge hp hmod u.1) q.frame (facetStarGauge hp hmod v.1) = oneFrame (m+1)) ∨
    (isOuter u.1 = true ∧ isOuter v.1 = true ∧
      facetStarLabel hp hmod v.1 = (reflectionFrame (minusParameters (m+1) hp hmod)).perm
        (facetStarLabel hp hmod u.1) ∧
      gauged (facetStarGauge hp hmod u.1) q.frame (facetStarGauge hp hmod v.1) =
        bridge (reflectionFrame (minusParameters (m+1) hp hmod)) (facetStarLabel hp hmod u.1)) := by
  let P := minusParameters (m+1) hp hmod
  obtain ⟨f,U⟩ := u
  obtain ⟨g,V⟩ := v
  cases f with
  | inl Aj =>
    obtain ⟨A,j⟩ := Aj
    cases g with
    | inl Bk =>
      obtain ⟨B,k⟩ := Bk
      have hh := generated_outer_outer_gauge hp hmod q hq A B j k U V ht
      right
      refine ⟨rfl,rfl,?_,hh⟩
      have hi : q.frame.perm j=k := ht.normal_index
      have hx := congrArg (fun F : RegisteredFrame (m+1) =>
        F.perm (facetStarLabel hp hmod (.inl (A,j)))) hh
      change (facetStarGauge hp hmod (.inl (B,k))).perm
        (q.frame.perm ((facetStarGauge hp hmod (.inl (A,j))).inverse
          ((facetStarGauge hp hmod (.inl (A,j))).perm j))) = _ at hx
      rw [RegisteredFrame.left_inverse,hi] at hx
      exact hx
    | inr k =>
      have he := generated_outer_inner_pose hp hmod q hq A j k U V ht
      have hf : q.frame = facetStarGauge hp hmod (.inl (A,j)) := by
        rw [he]
        exact incoming_frame_mu_one P rfl A.val (nativeCell_proper A)
      left
      refine ⟨rfl,?_,?_⟩
      · have hi : q.frame.perm j=k := ht.normal_index
        exact (hf ▸ hi).symm
      · change gauged (facetStarGauge hp hmod (.inl (A,j))) q.frame (oneFrame (m+1)) = _
        rw [hf]
        exact (frame_comp_one _).trans (frame_inv_comp _)
  | inr j =>
    cases g with
    | inl Bk =>
      obtain ⟨B,k⟩ := Bk
      have he := generated_outer_inner_pose hp hmod q.inv
        (generated_contact_inverse P q hq) B k j V U ht.registered_inverse
      have hf : q.inv.frame = facetStarGauge hp hmod (.inl (B,k)) := by
        rw [he]
        exact incoming_frame_mu_one P rfl B.val (nativeCell_proper B)
      left
      refine ⟨rfl,?_,?_⟩
      · have hi : q.inv.frame.perm k=j := ht.registered_inverse.normal_index
        rw [hf] at hi
        exact hi
      · change gauged (oneFrame (m+1)) q.frame _ = _
        rw [← hf]
        change gauged (oneFrame (m+1)) q.frame q.frame.inv = _
        change ((oneFrame (m+1)).inv.comp q.frame).comp q.frame.inv = _
        change ((oneFrame (m+1)).comp q.frame).comp q.frame.inv = _
        rw [frame_one_comp]
        exact frame_comp_inv _
    | inr k =>
      exact False.elim (generated_inner_inner_impossible hp hmod q hq j k U V ht)

#print axioms generated_native_classification

end
end PhysicalRegistration.NativeChair
