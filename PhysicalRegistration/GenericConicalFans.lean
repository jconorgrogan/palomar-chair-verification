module

public import PhysicalRegistration.PlacedConicalGerms

@[expose] public section

/-! Derived finite homogeneous fans at actual generic root crease points.
Only actual physical coverage and interior-disjointness are tiling inputs. -/
namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace Topology
open Set
noncomputable section

/-- The geometric origin of a cone constructed from actual native membership. -/
inductive ActualNativeCone {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x : Space m) : Set (Space m) → Prop
  | strictSide (u : Site m) (s : Side m)
      (hx : f.symm x ∈ keyGraph a u) (hs : f.symm x ∈ strictBranchRegion J u s) :
      ActualNativeCone a f x {z | ⟪placedNormal f (sideNormal a u s), z⟫_ℝ ≤ 0}
  | base (u : Site m) (s : Side m) (hx : f.symm x ∈ genericBaseCrease a u s) :
      ActualNativeCone a f x (twoHalfspaceCone (placedNormal f (outward u.1))
        (placedNormal f (sideNormal a u s)) (decide (0 < (a.value u : ℝ))))
  | side (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1)
      (hx : f.symm x ∈ genericSideCrease a u s t) :
      ActualNativeCone a f x (twoHalfspaceCone (placedNormal f (sideNormal a u s))
        (placedNormal f (sideNormal a u t)) (decide ((a.value u : ℝ) < 0)))
  | ordinary (hx : f.symm x ∈ frontier (body a))
      (hkey : ∀ u, f.symm x ∉ keyGraph a u) :
      ActualNativeCone a f x (placedCarrierCone f x)

/-- Output data for one actual incident cone. Its two-normal restriction and
membership germ are proved from boundary-plane control, never assumed. -/
structure ActualTwoNormalGerm {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x p q : Space m) where
  normals : Finset (Space m)
  cone : Set (Space m)
  card_le_two : normals.card ≤ 2
  normals_mem_span : ∀ n ∈ normals, n ∈ Submodule.span ℝ ({p, q} : Set (Space m))
  sign_determined : SignDetermined normals cone
  actual_germ : HasCenteredGerm (placedBody a f) x cone
  native_shape : ActualNativeCone a f x cone

/-- Classify every actual boundary incidence and construct its cone directly
from the native formulas, under a proved two-normal boundary-plane bound. -/
theorem exists_actualTwoNormalGerm_of_boundary_span
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hx : f.symm x ∈ frontier (body a))
    (hplanes : ∀ b : BoundaryPlaneIndex m, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    Nonempty (ActualTwoNormalGerm a f x p q) := by
  classical
  have hside (u : Site m) (s : Side m) (hs : f.symm x ∈ sideFace a u s) :
      placedNormal f (sideNormal a u s) ∈ Submodule.span ℝ ({p, q} : Set (Space m)) :=
    hplanes (.inr (u, s)) ⟨f.symm x, sideFace_plane a u s _ hs, f.apply_symm_apply x⟩
  by_cases hkey : ∃ u, f.symm x ∈ keyGraph a u
  · obtain ⟨u, hu⟩ := hkey
    rcases placed_keyGraph_stratum_of_boundary_normal_span hm a f u x p q hu hplanes with
      ⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, t, hst, hs⟩
    · refine ⟨⟨{placedNormal f (sideNormal a u s)}, _, by simp,
        ?_, ?_, placed_strictSide_hasCenteredGerm hm a f x u s hu hs,
        .strictSide u s hu hs⟩⟩
      · intro n hn
        simp only [Finset.mem_singleton] at hn
        subst n
        exact hside u s ⟨hu, strictBranchRegion_subset J u s hs⟩
      · intro z w h
        exact (h _ (by simp)).1
    · have hout : placedNormal f (outward u.1) ∈
          Submodule.span ℝ ({p, q} : Set (Space m)) := by
        obtain ⟨k, hk, hn⟩ := normalCoord_zero_boundaryPlane a u (f.symm x) hs.1.2
        have hv := hplanes (.inl (normalIndex u.1, k))
          ⟨f.symm x, hk, f.apply_symm_apply x⟩
        rw [hn, placedNormal, map_smul]
        exact Submodule.smul_mem _ _ hv
      refine ⟨⟨{placedNormal f (outward u.1), placedNormal f (sideNormal a u s)}, _,
        (by have h := Finset.card_insert_le (placedNormal f (outward u.1)) {placedNormal f (sideNormal a u s)}; simpa using h), ?_, twoHalfspaceCone_signDetermined _ _ _,
        placed_genericBase_hasCenteredGerm hm a f x u s hs, .base u s hs⟩⟩
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · exact hout
      · exact hside u s hs.1.1
    · refine ⟨⟨{placedNormal f (sideNormal a u s), placedNormal f (sideNormal a u t)}, _,
        (by have h := Finset.card_insert_le (placedNormal f (sideNormal a u s)) {placedNormal f (sideNormal a u t)}; simpa using h), ?_, twoHalfspaceCone_signDetermined _ _ _,
        placed_genericSide_hasCenteredGerm hm a f x u s t hs, .side u s t hst hs⟩⟩
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl
      · exact hside u s hs.1.1
      · exact hside u t hs.1.2
  · have hnone : ∀ u, f.symm x ∉ keyGraph a u := by simpa only [not_exists] using hkey
    obtain ⟨hcard, hspan⟩ := placedActiveCarrierNormals_span_card a f x p q hplanes
    exact ⟨⟨placedActiveCarrierNormals f x, placedCarrierCone f x, hcard, hspan,
      placedCarrierCone_signDetermined f x, placed_ordinary_hasCenteredGerm hm a f x hx hnone,
      .ordinary hx hnone⟩⟩

/-- A finite actual conical fan, constructed on the actual incident index set.
Both global coverage and disjoint cone interiors are derived by positive
scaling from the physical tiling on the common membership ball. -/
structure ActualFiniteConicalFan {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m) (x p q : Space m) where
  incident_finite : (incidentTiles a f x).Finite
  germs : (i : incidentTiles a f x) → ActualTwoNormalGerm a (f i.val) x p q
  radius : ℝ
  radius_pos : 0 < radius
  exact_membership : ∀ (i : incidentTiles a f x) z, ‖z‖ < radius →
    (x + z ∈ placedBody a (f i.val) ↔ z ∈ (germs i).cone)
  local_coverage : ∀ z, ‖z‖ < radius →
    ∃ i : incidentTiles a f x, x + z ∈ placedBody a (f i.val)
  cone_coverage : ∀ z, ∃ i : incidentTiles a f x, z ∈ (germs i).cone
  interiors_disjoint : Pairwise fun (i j : incidentTiles a f x) =>
    Disjoint (interior (germs i).cone) (interior (germs j).cone)

/-- Assemble actual local membership formulas on one common ball, then derive
full homogeneous cone coverage and pairwise disjoint interiors. -/
theorem PhysicalTiling.exists_actualFiniteConicalFan_of_boundary_span
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site m) (x p q : Space m)
    (hx : x ∈ placedKeyGraph a (f root) u)
    (hplanes : ∀ i, x ∈ placedBody a (f i) →
      ∀ b : BoundaryPlaneIndex m, x ∈ f i '' boundaryPlane a b →
        placedNormal (f i) (boundaryPlaneNormal a b) ∈
          Submodule.span ℝ ({p, q} : Set (Space m))) :
    Nonempty (ActualFiniteConicalFan a f x p q) := by
  classical
  obtain ⟨hfinite, U, hU, hxU, _, hcover, _⟩ := T.finite_incident_germ x
  let : Fintype (incidentTiles a f x) := hfinite.fintype
  have hex (i : incidentTiles a f x) : Nonempty (ActualTwoNormalGerm a (f i.val) x p q) := by
    have hworld := placedKeyGraph_incident_mem_frontier hm a f T.interiors_disjoint
      root u x hx i.val i.property
    have hpre : (f i.val).symm x ∈ frontier (body a) := by
      change x ∈ frontier ((f i.val).toHomeomorph '' body a) at hworld
      rw [← (f i.val).toHomeomorph.image_frontier] at hworld
      obtain ⟨y, hy, hxy⟩ := hworld
      simpa [← hxy] using hy
    exact exists_actualTwoNormalGerm_of_boundary_span hm a (f i.val) x p q hpre
      (hplanes i.val i.property)
  let g (i : incidentTiles a f x) : ActualTwoNormalGerm a (f i.val) x p q :=
    Classical.choice (hex i)
  choose r hr heq using fun i => (g i).actual_germ
  let W := U ∩ ⋂ i : incidentTiles a f x, Metric.ball x (r i)
  have hW : IsOpen W := hU.inter (isOpen_iInter_of_finite fun _ => Metric.isOpen_ball)
  have hxW : x ∈ W := ⟨hxU, mem_iInter.mpr fun i => Metric.mem_ball_self (hr i)⟩
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hW x hxW
  have hsmall (z : Space m) (hz : ‖z‖ < R) : x + z ∈ W :=
    hball (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
  have hcommon (i : incidentTiles a f x) (z : Space m) (hz : ‖z‖ < R) :
      x + z ∈ placedBody a (f i.val) ↔ z ∈ (g i).cone := by
    apply heq i z
    have hzi := mem_iInter.mp (hsmall z hz).2 i
    simpa [Metric.mem_ball, dist_eq_norm] using hzi
  have hlocal (z : Space m) (hz : ‖z‖ < R) :
      ∃ i : incidentTiles a f x, x + z ∈ placedBody a (f i.val) := by
    obtain ⟨i, hi, hmem⟩ := hcover (x + z) (hsmall z hz).1
    exact ⟨⟨i, hi⟩, hmem⟩
  refine ⟨⟨hfinite, g, R, hR, hcommon, hlocal, ?_, ?_⟩⟩
  · intro z
    obtain ⟨t, ht, htz⟩ := exists_pos_smul_norm_lt z hR
    obtain ⟨i, hi⟩ := hlocal (t • z) htz
    exact ⟨i, ((g i).sign_determined.homogeneous t ht z).mp ((hcommon i _ htz).mp hi)⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨t, ht, htz⟩ := exists_pos_smul_norm_lt z hR
    have hi := (g i).sign_determined.smul_mem_interior t ht hzi
    have hj := (g j).sign_determined.smul_mem_interior t ht hzj
    have hi' := (centeredGerm_interior_iff (placedBody a (f i.val))
      (g i).cone x R (hcommon i) (t • z) htz).mpr hi
    have hj' := (centeredGerm_interior_iff (placedBody a (f j.val))
      (g j).cone x R (hcommon j) (t • z) htz).mpr hj
    exact Set.disjoint_left.mp
      (T.interiors_disjoint (fun h => hij (Subtype.ext h))) hi' hj'

/-- One dense subset of a root base crease simultaneously supplies every
incident tile's actual two-normal cone and the full finite conical fan. -/
theorem PhysicalTiling.genericBaseCrease_actualFiniteConicalFan
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site m) (s : Side m) :
    ∃ D : Set (Space m), D ⊆ f root '' genericBaseCrease a u s ∧
      closure D = f root '' baseCrease a u s ∧
      ∀ x ∈ D, Nonempty (ActualFiniteConicalFan a f x
        (placedNormal (f root) (outward u.1))
        (placedNormal (f root) (sideNormal a u s))) := by
  obtain ⟨D, hDG, hDC, hspan⟩ :=
    genericBaseCrease_incident_boundary_normal_span a f T.interiors_disjoint root u s
  refine ⟨D, hDG, hDC, fun x hx => ?_⟩
  have hroot : x ∈ placedKeyGraph a (f root) u := by
    obtain ⟨y, hy, hxy⟩ := hDG hx
    exact ⟨y, hy.1.1.1, hxy⟩
  exact T.exists_actualFiniteConicalFan_of_boundary_span hm root u x _ _ hroot (hspan x hx)

/-- The same construction at every selected dense distinct-axis root side
crease point, with no separate generic set for any neighboring tile. -/
theorem PhysicalTiling.genericSideCrease_actualFiniteConicalFan
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    ∃ D : Set (Space m), D ⊆ f root '' genericSideCrease a u s t ∧
      closure D = f root '' sideCrease a u s t ∧
      ∀ x ∈ D, Nonempty (ActualFiniteConicalFan a f x
        (placedNormal (f root) (sideNormal a u s))
        (placedNormal (f root) (sideNormal a u t))) := by
  obtain ⟨D, hDG, hDC, hspan⟩ :=
    genericSideCrease_incident_boundary_normal_span a f T.interiors_disjoint root u s t hst
  refine ⟨D, hDG, hDC, fun x hx => ?_⟩
  have hroot : x ∈ placedKeyGraph a (f root) u := by
    obtain ⟨y, hy, hxy⟩ := hDG hx
    exact ⟨y, hy.1.1.1, hxy⟩
  exact T.exists_actualFiniteConicalFan_of_boundary_span hm root u x _ _ hroot (hspan x hx)

#print axioms PhysicalTiling.genericBaseCrease_actualFiniteConicalFan
#print axioms PhysicalTiling.genericSideCrease_actualFiniteConicalFan

end
end PhysicalRegistration.NativeChair
