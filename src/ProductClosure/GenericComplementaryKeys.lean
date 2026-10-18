module

public import ProductClosure.ConicalAngularCover
public import ProductClosure.NativeKeySectorMass
public import ProductClosure.OrdinarySectorMass
public import PhysicalRegistration.NonflatSectorBalance

@[expose] public section

/-!
# Actual generic complementary key incidences

The finite incident family is partitioned using actual key-graph membership.
Its actual angular conservation and the positive ordinary quarter-turn masses
force exactly two nonflat key incidences. Generic native base/side witnesses
are retained, rather than replaced with an abstract contact or angle premise.
-/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace Topology
open Set PhysicalRegistration MeasureTheory
open TransversePlaneCoordinates
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- An actual generic, nonflat key crease, with its native site and side labels. -/
def GenericKeyCrease {J : ℕ} [NeZero m] (a : Coefficients polyCells J)
    (f : Space m ≃ᵢ Space m) (x : Space m) : Prop :=
  ∃ u : Site polyCells, (∃ s : Side m, f.symm x ∈ genericBaseCrease a u s) ∨
    ∃ s t : Side m, s.1 ≠ t.1 ∧ f.symm x ∈ genericSideCrease a u s t

theorem GenericKeyCrease.mem_keyGraph {J : ℕ} [NeZero m]
    {a : Coefficients polyCells J} {f : Space m ≃ᵢ Space m} {x : Space m}
    (hx : GenericKeyCrease a f x) : ∃ u, f.symm x ∈ keyGraph a u := by
  obtain ⟨u, h⟩ := hx
  rcases h with ⟨s, hs⟩ | ⟨s, t, hst, hs⟩
  · exact ⟨u, hs.1.1.1⟩
  · exact ⟨u, hs.1.1.1⟩

/-- Nonflatness and the numerical key range come from the actual root germ. -/
theorem ActualTwoNormalGerm.transverseMass_genericKey_bounds
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) {a : Coefficients polyCells J}
    {f : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (hx : GenericKeyCrease a f x)
    (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ b : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ normalSpan p q) :
    3 * Real.pi / 4 < transverseMass p q h G.cone ∧
      transverseMass p q h G.cone < 5 * Real.pi / 4 ∧
      transverseMass p q h G.cone ≠ Real.pi := by
  obtain ⟨u, hx⟩ := hx
  rcases hx with ⟨s, hs⟩ | ⟨s, t, hst, hs⟩
  · exact G.transverseMass_base_bounds hm u s hs h hplanes
  · exact G.transverseMass_side_bounds hm u s t hst hs h hplanes

/-- Every actual key incidence is in the key range; strict side points are
allowed at this stage and have mass exactly pi. -/
theorem ActualNativeCone.transverseMass_key_bounds
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) {a : Coefficients polyCells J}
    {f : Space m ≃ᵢ Space m} {x p q : Space m} {C : Set (Space m)}
    (hC : ActualNativeCone a f x C) (hx : ∃ u, f.symm x ∈ keyGraph a u)
    (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ b : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ normalSpan p q) :
    3 * Real.pi / 4 < transverseMass p q h C ∧
      transverseMass p q h C < 5 * Real.pi / 4 := by
  rcases hC.transverseMass_cases hm h hplanes with he | hb | hord
  · rw [he]
    constructor <;> linarith [Real.pi_pos]
  · exact ⟨hb.1, hb.2.1⟩
  · obtain ⟨u, hu⟩ := hx
    exact (hord.2.1 u hu).elim

/-- A no-key actual incidence has a strictly positive integral quarter-turn
mass; neither positivity nor the mass formula is an input. -/
theorem ActualNativeCone.transverseMass_noKey_pos_quarters
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) {a : Coefficients polyCells J}
    {f : Space m ≃ᵢ Space m} {x p q : Space m} {C : Set (Space m)}
    (hC : ActualNativeCone a f x C) (hx : ¬ ∃ u, f.symm x ∈ keyGraph a u)
    (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ b : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ normalSpan p q) :
    ∃ k : ℕ, 0 < k ∧ transverseMass p q h C = k * (Real.pi / 2) := by
  cases hC with
  | strictSide u s hu hs => exact (hx ⟨u, hu⟩).elim
  | base u s hu => exact (hx ⟨u, hu.1.1.1⟩).elim
  | side u s t hst hu => exact (hx ⟨u, hu.1.1.1⟩).elim
  | ordinary hu hkey =>
    obtain ⟨k, hk, hmass⟩ := placedCarrierCone_volume_pos_quarters_of_boundary_span
      hm a f x p q h hu hkey hplanes
    refine ⟨k, hk, ?_⟩
    unfold transverseMass transverseDirections
    rw [hmass, ENNReal.toReal_ofReal (by positivity)]

/-- Once its actual mass is nonflat, an actual key cone must retain a generic
base or distinct-axis side description. -/
theorem ActualNativeCone.genericKey_of_nonflat
    {J : ℕ} [NeZero m] {a : Coefficients polyCells J}
    {f : Space m ≃ᵢ Space m} {x p q : Space m} {C : Set (Space m)}
    (hC : ActualNativeCone a f x C) (hx : ∃ u, f.symm x ∈ keyGraph a u)
    (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ b : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ normalSpan p q)
    (hne : transverseMass p q h C ≠ Real.pi) : GenericKeyCrease a f x := by
  cases hC with
  | strictSide u s hu hs =>
    apply (hne ?_).elim
    exact transverseMass_strictSide a f u s p q h
      (sideNormal_mem_rootSpan_of_boundary_span a f x p q hplanes u s
        ⟨hu, strictBranchRegion_subset J u s hs⟩)
  | base u s hu => exact ⟨u, Or.inl ⟨s, hu⟩⟩
  | side u s t hst hu => exact ⟨u, Or.inr ⟨s, t, hst, hu⟩⟩
  | ordinary hu hkey =>
    obtain ⟨u, hu⟩ := hx
    exact (hkey u hu).elim

/-- Two actual incident indices, exhaustive among all tiles at the point,
with retained native generic-crease witnesses and complementary actual mass. -/
structure ComplementaryKeyPair {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m} {x p q : Space m}
    (F : ActualFiniteConicalFan a f x p q) (h : LinearIndependent ℝ ![p, q])
    (root other : incidentTiles a f x) : Prop where
  distinct : other ≠ root
  exhaustive : ∀ i : incidentTiles a f x, i = root ∨ i = other
  root_crease : GenericKeyCrease a (f root.val) x
  other_crease : GenericKeyCrease a (f other.val) x
  root_nonflat : transverseMass p q h (F.germs root).cone ≠ Real.pi
  other_nonflat : transverseMass p q h (F.germs other).cone ≠ Real.pi
  mass_sum : transverseMass p q h (F.germs root).cone +
    transverseMass p q h (F.germs other).cone = 2 * Real.pi

/-- Actual angular conservation eliminates every ordinary incidence and
leaves exactly two nonflat key creases. All sums are derived from the fan. -/
theorem ActualFiniteConicalFan.two_genericKey_incidents
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m} {x p q : Space m}
    (F : ActualFiniteConicalFan a f x p q) (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ i, x ∈ placedBody a (f i) → ∀ b : BoundaryPlaneIndex polyCells,
      x ∈ f i '' boundaryPlane a b →
        placedNormal (f i) (boundaryPlaneNormal a b) ∈ normalSpan p q)
    (hroot : ∃ i : incidentTiles a f x, GenericKeyCrease a (f i.val) x) :
    (incidentTiles a f x).ncard = 2 ∧
      ∀ i : incidentTiles a f x, GenericKeyCrease a (f i.val) x ∧
        transverseMass p q h (F.germs i).cone ≠ Real.pi := by
  classical
  let : Fintype (incidentTiles a f x) := F.incident_finite.fintype
  let key (i : incidentTiles a f x) : Prop := ∃ u, (f i.val).symm x ∈ keyGraph a u
  let θ (i : incidentTiles a f x) := transverseMass p q h (F.germs i).cone
  let S : Finset (incidentTiles a f x) := Finset.univ.filter key
  let O : Finset (incidentTiles a f x) := Finset.univ.filter (fun i => ¬ key i)
  have hθ : ∀ i ∈ S, 3 * Real.pi / 4 < θ i ∧ θ i < 5 * Real.pi / 4 := by
    intro i hi
    exact (F.germs i).native_shape.transverseMass_key_bounds hm
      (Finset.mem_filter.mp hi).2 h (hplanes i.val i.property)
  have hroot' : ∃ i ∈ S, θ i ≠ Real.pi := by
    obtain ⟨i, hi⟩ := hroot
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.mem_keyGraph⟩,
      ((F.germs i).transverseMass_genericKey_bounds hm hi h (hplanes i.val i.property)).2.2⟩
  have hord : ∀ i : incidentTiles a f x, ∃ k : ℕ,
      (i ∈ O → 0 < k) ∧ (i ∈ O → θ i = k * (Real.pi / 2)) := by
    intro i
    by_cases hi : i ∈ O
    · obtain ⟨k, hk, hmass⟩ := (F.germs i).native_shape.transverseMass_noKey_pos_quarters hm
        (Finset.mem_filter.mp hi).2 h (hplanes i.val i.property)
      exact ⟨k, fun _ => hk, fun _ => hmass⟩
    · exact ⟨0, fun hi' => (hi hi').elim, fun hi' => (hi hi').elim⟩
  choose k hk hkmass using hord
  have hsum : (∑ i ∈ S, θ i) + (∑ i ∈ O, k i) * (Real.pi / 2) = 2 * Real.pi := by
    calc
      _ = (∑ i ∈ S, θ i) + ∑ i ∈ O, θ i := by
        congr 1
        rw [Nat.cast_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i hi => (hkmass i hi).symm)
      _ = ∑ i : incidentTiles a f x, θ i :=
        Finset.sum_filter_add_sum_filter_not _ _ _
      _ = 2 * Real.pi := F.angular_mass_sum_real h
  obtain ⟨hcard, hzero⟩ := sector_angle_balance_one_nonflat S θ (∑ i ∈ O, k i)
    hroot' hθ hsum
  have hO : O = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hki : k i ≤ ∑ j ∈ O, k j := Finset.single_le_sum (fun j hj => Nat.zero_le _) hi
    have hpos := hk i hi
    omega
  have hS : S = Finset.univ := by
    ext i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_contra hi
    have hiO : i ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    simp [hO] at hiO
  have hsumS : ∑ i ∈ S, θ i = 2 * Real.pi := by simpa [hzero] using hsum
  have hnonflat := complementary_pair_nonflat S θ hcard hsumS hroot'
  constructor
  · rw [hS, Finset.card_univ, Set.fintypeCard_eq_ncard] at hcard
    exact hcard
  · intro i
    have hi : i ∈ S := by rw [hS]; exact Finset.mem_univ _
    refine ⟨(F.germs i).native_shape.genericKey_of_nonflat
      (Finset.mem_filter.mp hi).2 h (hplanes i.val i.property) (hnonflat i hi), hnonflat i hi⟩


/-- A specified actual generic root has exactly one other incident tile.
Its genuine material sector is complementary and both crease descriptions
are retained. There is no angle-sum or contact-matching hypothesis. -/
theorem ActualFiniteConicalFan.unique_complementary_key
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m} {x p q : Space m}
    (F : ActualFiniteConicalFan a f x p q) (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ i, x ∈ placedBody a (f i) → ∀ b : BoundaryPlaneIndex polyCells,
      x ∈ f i '' boundaryPlane a b →
        placedNormal (f i) (boundaryPlaneNormal a b) ∈ normalSpan p q)
    (root : incidentTiles a f x) (hroot : GenericKeyCrease a (f root.val) x) :
    ∃! other : incidentTiles a f x, ComplementaryKeyPair F h root other := by
  classical
  let : Fintype (incidentTiles a f x) := F.incident_finite.fintype
  obtain ⟨hcard, hgeneric⟩ := F.two_genericKey_incidents hm h hplanes ⟨root, hroot⟩
  have hcard' : (Finset.univ : Finset (incidentTiles a f x)).card = 2 := by
    simpa only [Finset.card_univ, Set.fintypeCard_eq_ncard] using hcard
  obtain ⟨a₀, b₀, hab, huniv⟩ := Finset.card_eq_two.mp hcard'
  have hall (i : incidentTiles a f x) : i = a₀ ∨ i = b₀ := by
    simpa only [huniv, Finset.mem_insert, Finset.mem_singleton] using Finset.mem_univ i
  have hex : ∃ other : incidentTiles a f x, other ≠ root ∧
      ∀ i : incidentTiles a f x, i = root ∨ i = other := by
    rcases hall root with hr | hr
    · refine ⟨b₀, by simpa [hr] using hab.symm, ?_⟩
      intro i
      simpa [hr] using hall i
    · refine ⟨a₀, by simpa [hr] using hab, ?_⟩
      intro i
      simpa [hr, or_comm] using hall i
  obtain ⟨other, hother, hexhaust⟩ := hex
  have hpair : (Finset.univ : Finset (incidentTiles a f x)) = {root, other} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hexhaust i
  have hsum : transverseMass p q h (F.germs root).cone +
      transverseMass p q h (F.germs other).cone = 2 * Real.pi := by
    have hs := F.angular_mass_sum_real h
    change (∑ i : incidentTiles a f x, transverseMass p q h (F.germs i).cone) = _ at hs
    rw [hpair, Finset.sum_pair hother.symm] at hs
    exact hs
  refine ⟨other, ⟨hother, hexhaust, (hgeneric root).1, (hgeneric other).1,
    (hgeneric root).2, (hgeneric other).2, hsum⟩, ?_⟩
  intro j hj
  rcases hexhaust j with he | he
  · exact (hj.distinct he).elim
  · exact he

/-- The pair description identifies the full actual incident set in the
original tile index type, including all lower-dimensional incidences. -/
theorem ComplementaryKeyPair.incidentTiles_eq_pair
    {J : ℕ} [NeZero m] {ι : Type*} {a : Coefficients polyCells J}
    {f : ι → Space m ≃ᵢ Space m} {x p q : Space m}
    {F : ActualFiniteConicalFan a f x p q} {h : LinearIndependent ℝ ![p, q]}
    {root other : incidentTiles a f x} (H : ComplementaryKeyPair F h root other) :
    incidentTiles a f x = {root.val, other.val} := by
  ext i
  constructor
  · intro hi
    rcases H.exhaustive ⟨i, hi⟩ with he | he
    · exact Or.inl (congrArg Subtype.val he)
    · exact Or.inr (congrArg Subtype.val he)
  · rintro (rfl | rfl)
    · exact root.property
    · exact other.property

/-- At a dense subset of each actual placed base crease, all incident tiles
are exactly the root and its unique nonflat complementary key companion.
The same dense set retains the normal-span control for later angle rigidity. -/
theorem PhysicalTiling.genericBaseCrease_complementary_keys
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site polyCells) (s : Side m) :
    ∃ D : Set (Space m), D ⊆ f root '' genericBaseCrease a u s ∧
      closure D = f root '' baseCrease a u s ∧
      ∀ x ∈ D,
        (∀ i, x ∈ placedBody a (f i) → ∀ b : BoundaryPlaneIndex polyCells,
          x ∈ f i '' boundaryPlane a b → placedNormal (f i) (boundaryPlaneNormal a b) ∈
            normalSpan (placedNormal (f root) (outward u.1))
              (placedNormal (f root) (sideNormal a u s))) ∧
        (incidentTiles a f x).ncard = 2 ∧
        ∃ F : ActualFiniteConicalFan a f x (placedNormal (f root) (outward u.1))
            (placedNormal (f root) (sideNormal a u s)),
          ∃ hr : root ∈ incidentTiles a f x,
            ∃! other : incidentTiles a f x,
              ComplementaryKeyPair F (placed_base_normals_linearIndependent a u s (f root))
                ⟨root, hr⟩ other := by
  classical
  obtain ⟨D, hDG, hDC, hD⟩ := T.genericBaseCrease_angular_conservation hm root u s
  refine ⟨D, hDG, hDC, fun x hx => ?_⟩
  obtain ⟨hplanes, F, _⟩ := hD x hx
  obtain ⟨y, hy, hxy⟩ := hDG hx
  have hpre : (f root).symm x ∈ genericBaseCrease a u s := by simpa [← hxy] using hy
  have hr : root ∈ incidentTiles a f x := by
    apply (placedBody_isClosed a (f root)).frontier_subset
    exact placedKeyGraph_subset_frontier_placedBody hm a (f root) u ⟨y, hy.1.1.1, hxy⟩
  have hg : GenericKeyCrease a (f root) x := ⟨u, Or.inl ⟨s, hpre⟩⟩
  have hc := F.two_genericKey_incidents hm
    (placed_base_normals_linearIndependent a u s (f root)) hplanes ⟨⟨root, hr⟩, hg⟩
  exact ⟨hplanes, hc.1, F, hr, F.unique_complementary_key hm
    (placed_base_normals_linearIndependent a u s (f root)) hplanes ⟨root, hr⟩ hg⟩

/-- The same actual two-key and unique-complementarity conclusion on a dense
subset of every distinct-axis placed side crease. -/
theorem PhysicalTiling.genericSideCrease_complementary_keys
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1) :
    ∃ D : Set (Space m), D ⊆ f root '' genericSideCrease a u s t ∧
      closure D = f root '' sideCrease a u s t ∧
      ∀ x ∈ D,
        (∀ i, x ∈ placedBody a (f i) → ∀ b : BoundaryPlaneIndex polyCells,
          x ∈ f i '' boundaryPlane a b → placedNormal (f i) (boundaryPlaneNormal a b) ∈
            normalSpan (placedNormal (f root) (sideNormal a u s))
              (placedNormal (f root) (sideNormal a u t))) ∧
        (incidentTiles a f x).ncard = 2 ∧
        ∃ F : ActualFiniteConicalFan a f x (placedNormal (f root) (sideNormal a u s))
            (placedNormal (f root) (sideNormal a u t)),
          ∃ hr : root ∈ incidentTiles a f x,
            ∃! other : incidentTiles a f x,
              ComplementaryKeyPair F
                (placed_side_normals_linearIndependent a u s t hst (f root)) ⟨root, hr⟩ other := by
  classical
  obtain ⟨D, hDG, hDC, hD⟩ := T.genericSideCrease_angular_conservation hm root u s t hst
  refine ⟨D, hDG, hDC, fun x hx => ?_⟩
  obtain ⟨hplanes, F, _⟩ := hD x hx
  obtain ⟨y, hy, hxy⟩ := hDG hx
  have hpre : (f root).symm x ∈ genericSideCrease a u s t := by simpa [← hxy] using hy
  have hr : root ∈ incidentTiles a f x := by
    apply (placedBody_isClosed a (f root)).frontier_subset
    exact placedKeyGraph_subset_frontier_placedBody hm a (f root) u ⟨y, hy.1.1.1, hxy⟩
  have hg : GenericKeyCrease a (f root) x := ⟨u, Or.inr ⟨s, t, hst, hpre⟩⟩
  have hc := F.two_genericKey_incidents hm
    (placed_side_normals_linearIndependent a u s t hst (f root)) hplanes ⟨⟨root, hr⟩, hg⟩
  exact ⟨hplanes, hc.1, F, hr, F.unique_complementary_key hm
    (placed_side_normals_linearIndependent a u s t hst (f root)) hplanes ⟨root, hr⟩ hg⟩


/-- A generic key crease belongs to the literal placed native crease complex. -/
theorem GenericKeyCrease.mem_placed_creaseComplex
    {J : ℕ} [NeZero m] {a : Coefficients polyCells J}
    {f : Space m ≃ᵢ Space m} {x : Space m} (hx : GenericKeyCrease a f x) :
    ∃ u : Site polyCells, x ∈ f '' creaseComplex a u := by
  obtain ⟨u, hx⟩ := hx
  refine ⟨u, f.symm x, ?_, f.apply_symm_apply x⟩
  rcases hx with ⟨s, hs⟩ | ⟨s, t, hst, hs⟩
  · exact baseCrease_subset_creaseComplex a u s hs.1
  · exact sideCrease_subset_creaseComplex a u s t hst hs.1

/-- Erase the chart and fan while retaining an actual other-tile crease match. -/
theorem ComplementaryKeyPair.other_crease_match
    {J : ℕ} [NeZero m] {ι : Type*} {a : Coefficients polyCells J}
    {f : ι → Space m ≃ᵢ Space m} {x p q : Space m}
    {F : ActualFiniteConicalFan a f x p q} {h : LinearIndependent ℝ ![p, q]}
    {root other : incidentTiles a f x} (H : ComplementaryKeyPair F h root other) :
    ∃ i : ι, i ≠ root.val ∧ ∃ v : Site polyCells, x ∈ f i '' creaseComplex a v :=
  ⟨other.val, fun he => H.distinct (Subtype.ext he), H.other_crease.mem_placed_creaseComplex⟩

/-- Dense actual base-crease matches, in the direct form needed by connected
whole-feature propagation. No matching premise is supplied. -/
theorem PhysicalTiling.genericBaseCrease_dense_companions
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site polyCells) (s : Side m) :
    ∃ D : Set (Space m), closure D = f root '' baseCrease a u s ∧
      ∀ x ∈ D, ∃ i : ι, i ≠ root ∧ ∃ v : Site polyCells, x ∈ f i '' creaseComplex a v := by
  obtain ⟨D, _, hDC, hD⟩ := T.genericBaseCrease_complementary_keys hm root u s
  refine ⟨D, hDC, fun x hx => ?_⟩
  obtain ⟨_, _, F, hr, other, H, _⟩ := hD x hx
  exact H.other_crease_match

/-- Dense actual distinct-axis side-crease matches, with the same direct
whole-feature propagation interface. -/
theorem PhysicalTiling.genericSideCrease_dense_companions
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1) :
    ∃ D : Set (Space m), closure D = f root '' sideCrease a u s t ∧
      ∀ x ∈ D, ∃ i : ι, i ≠ root ∧ ∃ v : Site polyCells, x ∈ f i '' creaseComplex a v := by
  obtain ⟨D, _, hDC, hD⟩ := T.genericSideCrease_complementary_keys hm root u s t hst
  refine ⟨D, hDC, fun x hx => ?_⟩
  obtain ⟨_, _, F, hr, other, H, _⟩ := hD x hx
  exact H.other_crease_match

end
end ProductClosure.NativeCompiler
