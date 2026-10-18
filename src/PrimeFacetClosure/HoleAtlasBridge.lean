module
public import PrimeFacetClosure.MeanAtlasBridge
@[expose] public section
namespace RegisteredPrime.PrimeFacetClosure

/-- Generated contact membership is closed under reversing the actual
finite-supertile contact, independently of a contact catalog. -/
theorem generated_contact_inverse (P : Parameters) (e : Pose P.p)
    (he : GeneratedContact P e) : GeneratedContact P e.inv := by
  obtain ⟨n, q, r, hq, hr, hc, hs⟩ := he
  refine ⟨n, r, q, hr, hq, hc.symm, ?_⟩
  rw [← Pose.relative_reverse, hs.eq]
  exact Pose.Same.refl _

theorem incoming_arithmetic_atlas_contact (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    ArithmeticAtlasContact P (incomingPose P A hA) :=
  generated_arithmetic_atlas_contact P _ (incoming_generated P A hA)

theorem inverse_incoming_arithmetic_atlas_contact (P : Parameters) (A : Mask P.p)
    (hA : Proper A) : ArithmeticAtlasContact P (incomingPose P A hA).inv :=
  generated_arithmetic_atlas_contact P _
    (generated_contact_inverse P _ (incoming_generated P A hA))

theorem outgoing_seed_generated (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    GeneratedContact P (outgoingSeed P A hA) := by
  refine ⟨1, arithmeticChild P (.outer A hA), arithmeticChild P .central,
    child_is_descendant P (.outer A hA), child_is_descendant P .central,
    (central_outer_face_contact P A hA).symm, Pose.Same.refl _⟩

theorem outgoing_seed_arithmetic_atlas_contact (P : Parameters) (A : Mask P.p)
    (hA : Proper A) : ArithmeticAtlasContact P (outgoingSeed P A hA) :=
  generated_arithmetic_atlas_contact P _ (outgoing_seed_generated P A hA)

/-- Twice the literal inner-facet center, avoiding division in coordinates. -/
def innerFacetCenter2 {p : Nat} (k : Fin p) : Cell p :=
  fun i => 3 - if i = k then 1 else 0

/-- Twice the literal outer-facet center of occupied role A. -/
def outerFacetCenter2 {p : Nat} (A : Mask p) (j : Fin p) : Cell p :=
  fun i => 2 * bit (A i) + 1 + if i = j then 2 * bit (A j) - 1 else 0

/-- Actual affine action on doubled point coordinates; there is no cell
reflection correction because these are points, not unit-cell indices. -/
def mapPoint2 {p : Nat} (e : Pose p) (x : Cell p) : Cell p :=
  fun i => 2 * e.anchor i + e.frame.linear x i

@[simp] theorem mapPoint2_inv_mapPoint2 {p : Nat} (e : Pose p) (x : Cell p) :
    mapPoint2 e.inv (mapPoint2 e x) = x := by
  funext i
  simp only [mapPoint2, Pose.inv, RegisteredFrame.linear, RegisteredFrame.inv,
    RegisteredFrame.sign, e.frame.right_inverse]
  by_cases hn : e.frame.negative (e.frame.inverse i) = true <;> simp [hn] <;> omega

/-- The center equation at one inner/outer facet recovers every translation
coordinate once its actual full frame is the incoming frame. -/
theorem incoming_pose_of_frame_center (P : Parameters) (e : Pose P.p)
    (A : Mask P.p) (hA : Proper A) (j : Fin P.p)
    (hframe : e.frame = (incomingPose P A hA).frame)
    (hcenter : mapPoint2 e (innerFacetCenter2 (e.frame.perm j)) = outerFacetCenter2 A j) :
    e = incomingPose P A hA := by
  apply Pose.Same.eq
  refine ⟨fun i => congrArg (fun F : RegisteredFrame P.p => F.perm i) hframe,
    fun i => congrArg (fun F : RegisteredFrame P.p => F.negative i) hframe, ?_⟩
  intro i
  have hneg : e.frame.negative i = A i := by rw [hframe, incoming_negative]
  have hi := congrFun hcenter i
  have hperm : e.frame.perm i = e.frame.perm j ↔ i = j := by
    constructor
    · intro h
      have hh := congrArg e.frame.inverse h
      simpa only [e.frame.left_inverse] using hh
    · exact congrArg e.frame.perm
  rw [incoming_anchor]
  by_cases hij : i = j
  · subst i
    cases ha : A j <;>
      simp [mapPoint2, innerFacetCenter2, outerFacetCenter2,
        RegisteredFrame.linear, RegisteredFrame.sign, bit, hneg, ha] at hi ⊢ <;> omega
  · cases ha : A i <;>
      simp [mapPoint2, innerFacetCenter2, outerFacetCenter2, hperm,
        RegisteredFrame.linear, RegisteredFrame.sign, bit, hneg, ha, hij] at hi ⊢ <;> omega

/-- The reverse center equation recovers the exact inverse incoming pose. -/
theorem inverse_incoming_pose_of_frame_center (P : Parameters) (e : Pose P.p)
    (A : Mask P.p) (hA : Proper A) (j : Fin P.p)
    (hframe : e.inv.frame = (incomingPose P A hA).frame)
    (hcenter : mapPoint2 e (outerFacetCenter2 A j) =
      innerFacetCenter2 (e.frame.inverse j)) :
    e = (incomingPose P A hA).inv := by
  have hc := congrArg (mapPoint2 e.inv) hcenter
  rw [mapPoint2_inv_mapPoint2] at hc
  have he := incoming_pose_of_frame_center P e.inv A hA j hframe hc.symm
  have hi := congrArg Pose.inv he
  simpa only [Pose.inv_inv] using hi

/-- Incoming hole atlas membership is obtained from one actual matched
facet center and full frame, not from a support or atlas certificate. -/
theorem incoming_facet_arithmetic_atlas_contact (P : Parameters) (e : Pose P.p)
    (A : Mask P.p) (hA : Proper A) (j : Fin P.p)
    (hframe : e.frame = (incomingPose P A hA).frame)
    (hcenter : mapPoint2 e (innerFacetCenter2 (e.frame.perm j)) = outerFacetCenter2 A j) :
    ArithmeticAtlasContact P e := by
  rw [incoming_pose_of_frame_center P e A hA j hframe hcenter]
  exact incoming_arithmetic_atlas_contact P A hA

theorem inverse_incoming_facet_arithmetic_atlas_contact (P : Parameters) (e : Pose P.p)
    (A : Mask P.p) (hA : Proper A) (j : Fin P.p)
    (hframe : e.inv.frame = (incomingPose P A hA).frame)
    (hcenter : mapPoint2 e (outerFacetCenter2 A j) =
      innerFacetCenter2 (e.frame.inverse j)) : ArithmeticAtlasContact P e := by
  rw [inverse_incoming_pose_of_frame_center P e A hA j hframe hcenter]
  exact inverse_incoming_arithmetic_atlas_contact P A hA

/-- In the completed μ=1 rule the central frame is literally identity. -/
theorem central_frame_mu_one (P : Parameters) (hmu : P.mu = 1) :
    (arithmeticChild P .central).frame = (identityPose P.p).frame := by
  apply RegisteredFrame.ext_data
  · funext i
    apply Fin.ext
    change ((arithmeticChild P .central).frame.perm i).val = i.val
    rw [central_index_value, hmu, Nat.one_mul, Nat.mod_eq_of_lt i.isLt]
  · rfl

/-- Therefore the incoming hole frame is exactly the outer star gauge. -/
theorem incoming_frame_mu_one (P : Parameters) (hmu : P.mu = 1)
    (A : Mask P.p) (hA : Proper A) :
    (incomingPose P A hA).frame = (arithmeticChild P (.outer A hA)).frame := by
  have hc := central_frame_mu_one P hmu
  have hrole : incomingRole P A = A := by
    funext i
    simp [incomingRole, hc, identityPose]
  change (arithmeticChild P .central).frame.inv.comp
    (arithmeticChild P (.outer (incomingRole P A) (incomingRole_proper P A hA))).frame = _
  simp only [hc, hrole]
  apply RegisteredFrame.ext_data
  · rfl
  · funext i
    simp [RegisteredFrame.comp, RegisteredFrame.inv, identityPose]

/-- Direct μ=1 star-gauge form of the incoming hole bridge. -/
theorem incoming_facet_atlas_of_outer_frame (P : Parameters) (hmu : P.mu = 1)
    (e : Pose P.p) (A : Mask P.p) (hA : Proper A) (j : Fin P.p)
    (hframe : e.frame = (arithmeticChild P (.outer A hA)).frame)
    (hcenter : mapPoint2 e
      (innerFacetCenter2 ((arithmeticChild P (.outer A hA)).frame.perm j)) =
      outerFacetCenter2 A j) : ArithmeticAtlasContact P e := by
  apply incoming_facet_arithmetic_atlas_contact P e A hA j
    (hframe.trans (incoming_frame_mu_one P hmu A hA).symm)
  simpa only [hframe] using hcenter

/-- Direct μ=1 reverse star-gauge form of the outgoing hole bridge. -/
theorem inverse_incoming_facet_atlas_of_outer_frame (P : Parameters) (hmu : P.mu = 1)
    (e : Pose P.p) (A : Mask P.p) (hA : Proper A) (j : Fin P.p)
    (hframe : e.inv.frame = (arithmeticChild P (.outer A hA)).frame)
    (hcenter : mapPoint2 e (outerFacetCenter2 A j) =
      innerFacetCenter2 ((arithmeticChild P (.outer A hA)).frame.perm j)) :
    ArithmeticAtlasContact P e := by
  apply inverse_incoming_facet_arithmetic_atlas_contact P e A hA j
    (hframe.trans (incoming_frame_mu_one P hmu A hA).symm)
  have hp := congrArg (fun H : RegisteredFrame P.p => H.perm j) hframe
  change e.frame.inverse j = _ at hp
  rwa [hp]

/-- A matched pair of literal outer facet centers and a correctly labelled
odd frame bridge force the actual exterior-neighbor cell equation. -/
theorem outer_frame_center_shared_cell (P : Parameters) (e : Pose P.p)
    (A B : Mask P.p) (hA : Proper A) (hB : Proper B) (j : Fin P.p)
    (F : RegisteredFrame P.p)
    (hframe : (((arithmeticChild P (.outer A hA)).frame.inv.comp e.frame).comp
      (arithmeticChild P (.outer B hB)).frame) =
        bridge F ((arithmeticChild P (.outer A hA)).frame.perm j))
    (hcenter : mapPoint2 e (outerFacetCenter2 B (e.frame.perm j)) = outerFacetCenter2 A j) :
    e.cell (fun i => bit (B i)) = exterior A j := by
  have ht := outer_frame_transport_toggle P e A B hA hB j F hframe
  funext i
  have hi := congrFun hcenter i
  have hm := ht i
  have hperm : e.frame.perm i = e.frame.perm j ↔ i = j := by
    constructor
    · intro h
      have hh := congrArg e.frame.inverse h
      simpa only [e.frame.left_inverse] using hh
    · exact congrArg e.frame.perm
  by_cases hij : i = j
  · subst i
    cases ha : A j <;> cases hn : e.frame.negative j <;> cases hb : B (e.frame.perm j) <;>
      simp [mapPoint2, outerFacetCenter2, Pose.cell, RegisteredFrame.linear,
        RegisteredFrame.sign, exterior, wallToggle, bit, ha, hn, hb] at hi hm ⊢ <;> omega
  · cases ha : A i <;> cases hn : e.frame.negative i <;> cases hb : B (e.frame.perm i) <;>
      simp [mapPoint2, outerFacetCenter2, Pose.cell, RegisteredFrame.linear,
        RegisteredFrame.sign, exterior, wallToggle, bit, hperm, hij, ha, hn, hb] at hi hm ⊢ <;> omega

/-- Conversely every actual shared cell at a wall supplies exactly the
corresponding matched outer facet centers, including both empty endpoints. -/
theorem outer_centers_of_wall_shared_cell {p : Nat} (e : Pose p) (j : Fin p) (side : Bool)
    (hbox : boxLower e = wallBox j side) (A B : Mask p) (hs : A j = side)
    (hcell : e.cell (fun i => bit (B i)) = exterior A j) :
    mapPoint2 e (outerFacetCenter2 B (e.frame.perm j)) = outerFacetCenter2 A j := by
  have ht := (wall_shared_cell_iff e j side hbox A B hs).mp hcell
  funext i
  have hi := congrFun hcell i
  have hm := ht i
  have hperm : e.frame.perm i = e.frame.perm j ↔ i = j := by
    constructor
    · intro h
      have hh := congrArg e.frame.inverse h
      simpa only [e.frame.left_inverse] using hh
    · exact congrArg e.frame.perm
  by_cases hij : i = j
  · subst i
    cases ha : A j <;> cases hn : e.frame.negative j <;> cases hb : B (e.frame.perm j) <;>
      simp [mapPoint2, outerFacetCenter2, Pose.cell, RegisteredFrame.linear,
        RegisteredFrame.sign, exterior, wallToggle, bit, ha, hn, hb] at hi hm ⊢ <;> omega
  · cases ha : A i <;> cases hn : e.frame.negative i <;> cases hb : B (e.frame.perm i) <;>
      simp [mapPoint2, outerFacetCenter2, Pose.cell, RegisteredFrame.linear,
        RegisteredFrame.sign, exterior, wallToggle, bit, hperm, hij, ha, hn, hb] at hi hm ⊢ <;> omega

/-- The native center-only outer-facet interface: all actual matched
centers carry the correctly labelled odd gauged frame transport. -/
def OuterCenterFrameTransport (P : Parameters) (e : Pose P.p)
    (F : RegisteredFrame P.p) : Prop :=
  ∀ (A B : Mask P.p) (hA : Proper A) (hB : Proper B) (j : Fin P.p),
    mapPoint2 e (outerFacetCenter2 B (e.frame.perm j)) = outerFacetCenter2 A j →
    (((arithmeticChild P (.outer A hA)).frame.inv.comp e.frame).comp
      (arithmeticChild P (.outer B hB)).frame) =
        bridge F ((arithmeticChild P (.outer A hA)).frame.perm j)

/-- Direct center-to-atlas endpoint for an outer/outer profile mate. Its
only geometry input is a witnessed matched center; wall box and exact facet
availability are derived, then mean obstruction supplies the atlas clauses. -/
theorem outer_centers_arithmetic_atlas_contact (P : Parameters) (e : Pose P.p)
    (F : RegisteredFrame P.p) (hF : F.AffineIndex)
    (hF0 : F.perm (zeroIndex P) = zeroIndex P)
    (ht : OuterCenterFrameTransport P e F)
    (hwitness : ∃ (A B : Mask P.p) (_hA : Proper A) (_hB : Proper B) (j : Fin P.p),
      mapPoint2 e (outerFacetCenter2 B (e.frame.perm j)) = outerFacetCenter2 A j) :
    ArithmeticAtlasContact P e := by
  obtain ⟨A, B, hA, hB, j, hcenter⟩ := hwitness
  have hf := ht A B hA hB j hcenter
  have hc := outer_frame_center_shared_cell P e A B hA hB j F hf hcenter
  have hb := outer_frame_transport_wall_box P e A B hA hB j F hc hf
  apply wall_arithmetic_atlas_of_frame_transport P e j (A j) F hb hF hF0
  intro C D hC hD hs hcell
  exact ⟨(arithmeticChild P (.outer C hC)).frame.perm j,
    ht C D hC hD j (outer_centers_of_wall_shared_cell e j (A j) hb C D hs hcell)⟩

/-- The reflected inner/inner bridge forces identical side-two carrier
boxes. It is not an admissible disjoint contact. -/
theorem inner_bridge_box_zero {p : Nat} (e : Pose p) (F : RegisteredFrame p) (k : Fin p)
    (hframe : e.frame = bridge F k)
    (hcenter : mapPoint2 e (innerFacetCenter2 (F.perm k)) = innerFacetCenter2 k) :
    boxLower e = (fun _ => 0) := by
  funext i
  have hi := congrFun hcenter i
  have hperm : F.perm i = F.perm k ↔ i = k := by
    constructor
    · intro h
      have hh := congrArg F.inverse h
      simpa only [F.left_inverse] using hh
    · exact congrArg F.perm
  by_cases hik : i = k <;>
    simp [mapPoint2, innerFacetCenter2, boxLower, RegisteredFrame.linear,
      RegisteredFrame.sign, hframe, bridge, bit, hperm, hik] at hi ⊢ <;> omega

/-- Inner/inner full-profile matching is excluded by actual carrier
nonoverlap, using a constructed common occupied cell. -/
theorem inner_bridge_not_disjoint (P : Parameters) (e : Pose P.p)
    (F : RegisteredFrame P.p) (k : Fin P.p) (hframe : e.frame = bridge F k)
    (hcenter : mapPoint2 e (innerFacetCenter2 (F.perm k)) = innerFacetCenter2 k) :
    ¬ Disjoint (identityPose P.p) e := by
  intro hd
  have hb : boxLower (identityPose P.p) = boxLower e := by
    rw [inner_bridge_box_zero e F k hframe hcenter]
    rfl
  obtain ⟨l, hlk, _⟩ := third_axis (P.prime.three_le P.odd) k k
  obtain ⟨c, hc⟩ := same_box_overlap (identityPose P.p) e l k hlk hb
  exact hd c hc

#print axioms incoming_arithmetic_atlas_contact
#print axioms inverse_incoming_arithmetic_atlas_contact
#print axioms outgoing_seed_arithmetic_atlas_contact
#print axioms incoming_pose_of_frame_center
#print axioms inverse_incoming_pose_of_frame_center
#print axioms incoming_facet_atlas_of_outer_frame
#print axioms inverse_incoming_facet_atlas_of_outer_frame
#print axioms outer_centers_arithmetic_atlas_contact
#print axioms inner_bridge_not_disjoint
end RegisteredPrime.PrimeFacetClosure
