module

public import PrimeFacetClosure.NativeWalkTransport
public import RegisteredPrime.PoseAlgebra

@[expose] public section

/-! The actual isometry path product and its complete registered frame agree.
Consequently odd opposite-coefficient candidates inherit the star normal form.
Only generator-level real/registered binding is used; candidate/path equality
and all finite-path conclusions are proved. -/
namespace PhysicalRegistration.NativeChair.NativeWalkTransport
noncomputable section
open RegisteredPrime
open RegisteredPrime.PrimeFacetClosure
open RegisteredPrime.PrimeFacetClosure.StarHolonomy

/-- Exact real-coordinate meaning of the entire registered linear frame. -/
def RegisteredFrameRealizes {m : ℕ} (F : RegisteredFrame (m+1))
    (e : Space m ≃ᵢ Space m) : Prop :=
  ∀ (x : Space m) (i : Fin (m+1)), placedNormal e x i = (F.sign i : ℝ) * x (F.perm i)

theorem poseRealizes_frame {m : ℕ} {q : Pose (m+1)} {e : Space m ≃ᵢ Space m}
    (h : RegisteredPoseRealizes q e) : RegisteredFrameRealizes q.frame e := by
  intro x i
  rw [placedNormal_eq_sub_zero]
  change e x i - e 0 i = _
  rw [h x i, h 0 i]
  simp

/-- The row-coordinate semantics is faithful: signs and the complete index
permutation are recovered, rather than merely a normal-sign character. -/
theorem frameRealizes_unique {m : ℕ} {F H : RegisteredFrame (m+1)}
    {e : Space m ≃ᵢ Space m} (hF : RegisteredFrameRealizes F e)
    (hH : RegisteredFrameRealizes H e) : F = H := by
  have he (x : Space m) (i : Fin (m+1)) :
      (F.sign i : ℝ) * x (F.perm i) = (H.sign i : ℝ) * x (H.perm i) :=
    (hF x i).symm.trans (hH x i)
  apply frame_ext
  · funext i
    by_contra hn
    let x : Space m := WithLp.toLp 2 (fun j => if j = F.perm i then (1 : ℝ) else 0)
    have h := he x i
    have hn' : H.perm i ≠ F.perm i := Ne.symm hn
    change (F.sign i : ℝ) * (if F.perm i = F.perm i then 1 else 0) =
      (H.sign i : ℝ) * (if H.perm i = F.perm i then 1 else 0) at h
    simp [hn'] at h
    cases hf : F.negative i <;> norm_num [RegisteredFrame.sign, hf] at h
  · funext i
    let x : Space m := WithLp.toLp 2 (fun _ => (1 : ℝ))
    have h := he x i
    change (F.sign i : ℝ) * 1 = (H.sign i : ℝ) * 1 at h
    cases hf : F.negative i <;> cases hh : H.negative i <;>
      simp_all [RegisteredFrame.sign] <;> norm_num at h

@[simp] theorem frameRealizes_identity {m : ℕ} :
    RegisteredFrameRealizes (oneFrame (m+1)) (IsometryEquiv.refl (Space m)) := by
  intro x i
  rw [placedNormal_refl]
  simp [oneFrame, identityPose, RegisteredFrame.sign]

theorem frameRealizes_comp {m : ℕ} {F H : RegisteredFrame (m+1)}
    {f g : Space m ≃ᵢ Space m} (hF : RegisteredFrameRealizes F f)
    (hH : RegisteredFrameRealizes H g) :
    RegisteredFrameRealizes (F.comp H) (g.trans f) := by
  intro x i
  rw [placedNormal_comp, hF, hH]
  rw [RegisteredFrame.comp_sign]
  simp only [Int.cast_mul, RegisteredFrame.comp]
  ring

/-- The product of the registered edge frames realizes the product of the
actual edge isometries. Its only binding premise is checked on generators. -/
theorem walk_frame_realizes {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {F : RegisteredFrame (m+1)} (S : StarGauge (contactGraph A hA) F)
    (he : ∀ {u v} (h : (contactGraph A hA).Adj u v),
      RegisteredFrameRealizes (S.edgeFrame h) (edgePlacement A hA h))
    {u v : Site m} (w : (contactGraph A hA).Walk u v) :
    RegisteredFrameRealizes (S.transport w) (walkPlacement A hA w) := by
  induction w with
  | nil => exact frameRealizes_identity
  | cons h w ih => exact frameRealizes_comp (he h) ih

/-- Candidate and graph path have the identical complete registered frame,
proved via their identical actual isometry and faithful coordinate semantics. -/
theorem odd_walk_candidate_frame {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {F : RegisteredFrame (m+1)} (S : StarGauge (contactGraph A hA) F)
    (hedge : ∀ {u v} (h : (contactGraph A hA).Adj u v),
      RegisteredFrameRealizes (S.edgeFrame h) (edgePlacement A hA h))
    {u v : Site m} (w : (contactGraph A hA).Walk u v) (hw : w.length % 2 = 1)
    {q : Pose (m+1)} {e : Space m ≃ᵢ Space m}
    (hq : RegisteredPoseRealizes q e) (he : SiteTransport e u v) :
    q.frame = S.transport w := by
  have hp := walk_frame_realizes A hA S hedge w
  rw [odd_walk_equals_candidate A hA w hw he] at hp
  exact frameRealizes_unique (poseRealizes_frame hq) hp

/-- The exact normal form applies to the independently recovered candidate
itself, not only to an unrelated graph product. -/
theorem opposite_coefficients_candidate_frame
    {m : ℕ} [LinearOrder (Site m)]
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {F : RegisteredFrame (m+1)} (S : StarGauge (contactGraph A hA) F)
    (hedge : ∀ {u v} (h : (contactGraph A hA).Adj u v),
      RegisteredFrameRealizes (S.edgeFrame h) (edgePlacement A hA h))
    {u v : Site m} {q : Pose (m+1)} {e : Space m ≃ᵢ Space m}
    (hq : RegisteredPoseRealizes q e) (he : SiteTransport e u v)
    (ha : (graphCoefficients (contactGraph A hA)).value v =
      -(graphCoefficients (contactGraph A hA)).value u)
    (ht : S.outer u = S.outer v) :
    S.label v = F.perm (S.label u) ∧
      q.frame = ((S.gauge u).comp (bridge F (S.label u))).comp (S.gauge v).inv := by
  obtain ⟨w, hw⟩ := opposite_coefficients_odd_walk A hA ha
  have hf := odd_walk_candidate_frame A hA S hedge w hw hq he
  exact ⟨(S.odd_same_type w ht hw).1, hf.trans (S.odd_same_type_ambient w ht hw)⟩

/-- The inner/outer counterpart is the precise hole-frame normal form. -/
theorem opposite_coefficients_candidate_hole_frame
    {m : ℕ} [LinearOrder (Site m)]
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {F : RegisteredFrame (m+1)} (S : StarGauge (contactGraph A hA) F)
    (hedge : ∀ {u v} (h : (contactGraph A hA).Adj u v),
      RegisteredFrameRealizes (S.edgeFrame h) (edgePlacement A hA h))
    {u v : Site m} {q : Pose (m+1)} {e : Space m ≃ᵢ Space m}
    (hq : RegisteredPoseRealizes q e) (he : SiteTransport e u v)
    (ha : (graphCoefficients (contactGraph A hA)).value v =
      -(graphCoefficients (contactGraph A hA)).value u)
    (ht : S.outer u ≠ S.outer v) :
    S.label v = S.label u ∧ q.frame = (S.gauge u).comp (S.gauge v).inv := by
  obtain ⟨w, hw, hl, hf⟩ := opposite_coefficients_different_type_transport A hA S ha ht
  exact ⟨hl, (odd_walk_candidate_frame A hA S hedge w hw hq he).trans hf⟩


/-- Site transport also matches the undecorated carrier facet centers, because
the entire asymmetric free-orbit offset is carried by the tangent equations. -/
theorem siteTransport_facetCenter {m : ℕ} {e : Space m ≃ᵢ Space m} {u v : Site m}
    (he : SiteTransport e u v) : e (facetCenter v.1) = facetCenter u.1 := by
  have hoff : placedNormal e (siteOffset v) = siteOffset u := by
    simp only [siteOffset, placedNormal, map_sum, map_smul]
    exact Finset.sum_congr rfl (fun j _ => congrArg (q0 j • ·) (he.1 j))
  have hc := he.2.2
  simp only [siteCenter] at hc
  change e.toRealAffineIsometryEquiv (facetCenter v.1 + siteOffset v) = _ at hc
  rw [affineIsometry_map_add] at hc
  change e (facetCenter v.1) + placedNormal e (siteOffset v) = _ at hc
  rw [hoff] at hc
  exact add_right_cancel hc

/-- Translation is recovered from the genuine facet-center equation; offsets
are retained rather than quotiented out. -/
theorem candidate_anchor {m : ℕ} {q : Pose (m+1)} {e : Space m ≃ᵢ Space m}
    {u v : Site m} (hq : RegisteredPoseRealizes q e) (he : SiteTransport e u v)
    (i : Fin (m+1)) :
    (q.anchor i : ℝ) = facetCenter u.1 i -
      (q.frame.sign i : ℝ) * facetCenter v.1 (q.frame.perm i) := by
  have h := hq (facetCenter v.1) i
  rw [siteTransport_facetCenter he] at h
  linarith

/-- Complete site transport itself implies an integral signed-permutation
placement, before any star classification is imposed. -/
theorem siteTransport_integral {m : ℕ} {e : Space m ≃ᵢ Space m} {u v : Site m}
    (he : SiteTransport e u v) : HasIntegralSignedPermutation e := by
  have h := relativePlacement_integral_signed_permutation u v
    (IsometryEquiv.refl (Space m)) e
    (fun j => by simpa only [placedNormal_refl] using he.1 j)
    (by simpa only [placedNormal_refl] using he.2.1)
    he.2.2.symm
  have hid : relativePlacement (IsometryEquiv.refl (Space m)) e = e := by
    apply IsometryEquiv.ext
    intro x
    rfl
  rwa [hid] at h

/-- A canonical full registered pose for every genuine directed native edge.
Its existence comes from physical site transport, not from graph closure. -/
def edgePose {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (h : (contactGraph A hA).Adj u v) : Pose (m+1) :=
  (exists_registeredPoseRealizes (edgePlacement A hA h)
    (siteTransport_integral (edgePlacement_spec A hA h))).choose

theorem edgePose_realizes {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (h : (contactGraph A hA).Adj u v) :
    RegisteredPoseRealizes (edgePose A hA h) (edgePlacement A hA h) :=
  (exists_registeredPoseRealizes (edgePlacement A hA h)
    (siteTransport_integral (edgePlacement_spec A hA h))).choose_spec

/-- The canonical native star-gauge constructor. Its sole unproved geometric
input is the local hole/wall classification in the chosen gauges; the edge
frames and their physical interpretation are constructed automatically. -/
def nativeStarGauge {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    (F : RegisteredFrame (m+1)) (hF : ∀ k, F.perm (F.perm k) = k)
    (label : Site m → Fin (m+1)) (outer : Site m → Bool)
    (gauge : Site m → RegisteredFrame (m+1))
    (hclass : ∀ {u v} (h : (contactGraph A hA).Adj u v),
      (outer v = !outer u ∧ label v = label u ∧
        gauged (gauge u) (edgePose A hA h).frame (gauge v) = oneFrame (m+1)) ∨
      (outer u = true ∧ outer v = true ∧ label v = F.perm (label u) ∧
        gauged (gauge u) (edgePose A hA h).frame (gauge v) = bridge F (label u))) :
    StarGauge (contactGraph A hA) F where
  involutive := hF
  label := label
  outer := outer
  gauge := gauge
  edgeFrame := fun h => (edgePose A hA h).frame
  edge_classification := hclass

/-- Canonical edge-frame binding is proved, so users of `nativeStarGauge` do
not need to assume a registered/physical compatibility theorem. -/
theorem nativeStarGauge_realizes {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    (F : RegisteredFrame (m+1)) (hF : ∀ k, F.perm (F.perm k) = k)
    (label : Site m → Fin (m+1)) (outer : Site m → Bool)
    (gauge : Site m → RegisteredFrame (m+1)) (hclass)
    {u v : Site m} (h : (contactGraph A hA).Adj u v) :
    RegisteredFrameRealizes
      ((nativeStarGauge A hA F hF label outer gauge hclass).edgeFrame h)
      (edgePlacement A hA h) :=
  poseRealizes_frame (edgePose_realizes A hA h)

#print axioms frameRealizes_unique
#print axioms candidate_anchor
#print axioms siteTransport_integral
#print axioms nativeStarGauge_realizes
#print axioms walk_frame_realizes
#print axioms opposite_coefficients_candidate_frame
#print axioms opposite_coefficients_candidate_hole_frame
end
end PhysicalRegistration.NativeChair.NativeWalkTransport
