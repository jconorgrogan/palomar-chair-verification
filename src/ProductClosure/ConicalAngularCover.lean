module

public import ProductClosure.ConicalFanRegularity
public import ProductClosure.SignConeInterior
public import ProductClosure.TransversePlaneCoordinates
public import PhysicalRegistration.PlanarSectorMeasure

@[expose] public section

/-! Actual angular conservation for the finite conical fan derived from a
physical tiling. Normal-span coordinates, finite exceptional directions, and
ambient interior-disjointness supply the measure partition. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace Topology
open Set PhysicalRegistration MeasureTheory
open TransversePlaneCoordinates PlanarSectorMeasure
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Restriction of an actual ambient cone to unit directions in the proved
crease-normal plane. -/
def angularCone  (p q : Space m) (h : LinearIndependent ℝ ![p, q])
    (C : Set (Space m)) : Set Real.Angle :=
  {θ | lift p q h (direction θ) ∈ C}

/-- Only finitely many directions lie in any nonzero listed normal plane. -/
theorem finite_angular_normal_zeros  (p q : Space m)
    (h : LinearIndependent ℝ ![p, q]) (n : Space m)
    (hn : n ∈ normalSpan p q) (hne : n ≠ 0) :
    {θ : Real.Angle | ⟪n, lift p q h (direction θ)⟫_ℝ = 0}.Finite := by
  have heq : {θ : Real.Angle | ⟪n, lift p q h (direction θ)⟫_ℝ = 0} =
      {θ : Real.Angle | ⟪normal p q h n hn, direction θ⟫_ℝ = 0} := by
    ext θ
    rw [mem_ofPred_eq, mem_ofPred_eq, inner_normal_lift]
  rw [heq]
  exact finite_normal_boundary (by simpa using hne)

/-- Angular preimages of actual closed cones are measurable. -/
theorem measurableSet_angularCone  (p q : Space m)
    (h : LinearIndependent ℝ ![p, q]) (C : Set (Space m)) (hC : IsClosed C) :
    MeasurableSet (angularCone p q h C) := by
  have hd : Continuous direction := by
    unfold direction
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_cos
    · exact Real.Angle.continuous_sin
  exact (hC.preimage ((lift p q h).continuous.comp hd)).measurableSet

/-- For the actual finite fan, every overlapping pair of angular sectors has
zero measure. Off finitely many normal zeros, membership is ambient interior
membership, contradicted by the physical tiling's derived disjointness. -/
theorem ActualFiniteConicalFan.angular_pairwise_aeDisjoint
    {J : ℕ} [NeZero m] {ι : Type*} {a : Coefficients polyCells J}
    {f : ι → Space m ≃ᵢ Space m} {x p q : Space m}
    (F : ActualFiniteConicalFan a f x p q) (h : LinearIndependent ℝ ![p, q]) :
    Pairwise fun i j : incidentTiles a f x =>
      AEDisjoint volume (angularCone p q h (F.germs i).cone)
        (angularCone p q h (F.germs j).cone) := by
  classical
  intro i j hij
  let E (k : incidentTiles a f x) : Set Real.Angle :=
    ⋃ n ∈ (F.germs k).normals,
      if n = 0 then ∅ else {θ | ⟪n, lift p q h (direction θ)⟫_ℝ = 0}
  have hE (k : incidentTiles a f x) : (E k).Finite := by
    apply (F.germs k).normals.finite_toSet.biUnion
    intro n hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · simpa [hn0] using finite_angular_normal_zeros p q h n
        ((F.germs k).normals_mem_span n hn) hn0
  apply measure_mono_null (t := E i ∪ E j) _ (((hE i).union (hE j)).measure_zero volume)
  intro θ hθ
  by_contra hnot
  have hoff (k : incidentTiles a f x) (hk : θ ∉ E k) :
      ∀ n ∈ (F.germs k).normals, n ≠ 0 →
        ⟪n, lift p q h (direction θ)⟫_ℝ ≠ 0 := by
    intro n hn hn0 heq
    apply hk
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn, by simp [hn0, heq]⟩⟩
  have hi := (F.germs i).sign_determined.mem_interior_of_off_normals hθ.1
    (hoff i (fun hi => hnot (Or.inl hi)))
  have hj := (F.germs j).sign_determined.mem_interior_of_off_normals hθ.2
    (hoff j (fun hj => hnot (Or.inr hj)))
  exact Set.disjoint_left.mp (F.interiors_disjoint hij) hi hj

/-- The actual incident cone masses add to a full turn. Coverage and the
finite exceptional overlap calculation are derived from the physical fan. -/
theorem ActualFiniteConicalFan.angular_mass_sum
    {J : ℕ} [NeZero m] {ι : Type*} {a : Coefficients polyCells J}
    {f : ι → Space m ≃ᵢ Space m} {x p q : Space m}
    (F : ActualFiniteConicalFan a f x p q) (h : LinearIndependent ℝ ![p, q]) :
    let : Fintype (incidentTiles a f x) := F.incident_finite.fintype
    ∑ i : incidentTiles a f x, volume (angularCone p q h (F.germs i).cone) =
      ENNReal.ofReal (2 * Real.pi) := by
  classical
  let : Fintype (incidentTiles a f x) := F.incident_finite.fintype
  dsimp only
  have hc : (⋃ i : incidentTiles a f x, angularCone p q h (F.germs i).cone) = univ := by
    apply eq_univ_of_forall
    intro θ
    obtain ⟨i, hi⟩ := F.cone_coverage (lift p q h (direction θ))
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hm := measure_iUnion₀ (F.angular_pairwise_aeDisjoint h)
    (fun i => (measurableSet_angularCone p q h _ (F.germs i).cone_isClosed).nullMeasurableSet)
  rw [hc, tsum_fintype] at hm
  rw [← hm]
  exact AddCircle.measure_univ (2 * Real.pi)

/-- Real-valued angular conservation for the literal actual incident cones. -/
theorem ActualFiniteConicalFan.angular_mass_sum_real
    {J : ℕ} [NeZero m] {ι : Type*} {a : Coefficients polyCells J}
    {f : ι → Space m ≃ᵢ Space m} {x p q : Space m}
    (F : ActualFiniteConicalFan a f x p q) (h : LinearIndependent ℝ ![p, q]) :
    let : Fintype (incidentTiles a f x) := F.incident_finite.fintype
    ∑ i : incidentTiles a f x, (volume (angularCone p q h (F.germs i).cone)).toReal =
      2 * Real.pi := by
  classical
  let : Fintype (incidentTiles a f x) := F.incident_finite.fintype
  dsimp only
  have he := congrArg ENNReal.toReal (F.angular_mass_sum h)
  rw [ENNReal.toReal_sum (fun i _ => measure_ne_top volume _),
    ENNReal.toReal_ofReal Real.two_pi_pos.le] at he
  exact he

/-- A dense actual root base crease has a full-turn sum of actual incident
material-sector masses. The same selected set retains the proved incident
boundary-normal span condition needed to identify each individual mass. -/
theorem PhysicalTiling.genericBaseCrease_angular_conservation
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
        ∃ F : ActualFiniteConicalFan a f x (placedNormal (f root) (outward u.1))
            (placedNormal (f root) (sideNormal a u s)),
          let : Fintype (incidentTiles a f x) := F.incident_finite.fintype
          ∑ i : incidentTiles a f x,
            (volume (angularCone _ _ (placed_base_normals_linearIndependent a u s (f root))
              (F.germs i).cone)).toReal = 2 * Real.pi := by
  classical
  obtain ⟨D, hDG, hDC, hspan⟩ :=
    genericBaseCrease_incident_boundary_normal_span a f T.interiors_disjoint root u s
  refine ⟨D, hDG, hDC, fun x hx => ⟨hspan x hx, ?_⟩⟩
  have hroot : x ∈ placedKeyGraph a (f root) u := by
    obtain ⟨y, hy, hxy⟩ := hDG hx
    exact ⟨y, hy.1.1.1, hxy⟩
  obtain ⟨F⟩ := T.exists_actualFiniteConicalFan_of_boundary_span hm root u x _ _ hroot
    (hspan x hx)
  exact ⟨F, F.angular_mass_sum_real (placed_base_normals_linearIndependent a u s (f root))⟩

/-- The same actual angular conservation on one dense distinct-axis root
side crease, retaining the identical incident-plane span information. -/
theorem PhysicalTiling.genericSideCrease_angular_conservation
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
        ∃ F : ActualFiniteConicalFan a f x (placedNormal (f root) (sideNormal a u s))
            (placedNormal (f root) (sideNormal a u t)),
          let : Fintype (incidentTiles a f x) := F.incident_finite.fintype
          ∑ i : incidentTiles a f x,
            (volume (angularCone _ _ (placed_side_normals_linearIndependent a u s t hst (f root))
              (F.germs i).cone)).toReal = 2 * Real.pi := by
  classical
  obtain ⟨D, hDG, hDC, hspan⟩ :=
    genericSideCrease_incident_boundary_normal_span a f T.interiors_disjoint root u s t hst
  refine ⟨D, hDG, hDC, fun x hx => ⟨hspan x hx, ?_⟩⟩
  have hroot : x ∈ placedKeyGraph a (f root) u := by
    obtain ⟨y, hy, hxy⟩ := hDG hx
    exact ⟨y, hy.1.1.1, hxy⟩
  obtain ⟨F⟩ := T.exists_actualFiniteConicalFan_of_boundary_span hm root u x _ _ hroot
    (hspan x hx)
  exact ⟨F, F.angular_mass_sum_real (placed_side_normals_linearIndependent a u s t hst (f root))⟩

end
end ProductClosure.NativeCompiler
