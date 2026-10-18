module

public import ProductClosure.OrdinaryConeActiveNormals
public import PhysicalRegistration.TransversePlaneCoordinates
public import PhysicalRegistration.PlanarSectorMeasure

@[expose] public section

/-!
# Actual quarter-turn masses of ordinary carrier cones

The angular mass is derived from the literal carrier sign formula. A single
active axis is completed by its planar perpendicular; two active axes are
already orthogonal. A strict inward vector proves that at least one genuine
open quadrant is accepted.
-/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace Topology
open Set MeasureTheory PhysicalRegistration
open TransversePlaneCoordinates PlanarSectorMeasure
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- The concrete perpendicular completes any nonzero planar normal. -/
def planePerp (n : PlanarSectorMeasure.Plane) : PlanarSectorMeasure.Plane :=
  WithLp.toLp 2 ![-n 1, n 0]

theorem planePerp_ne_zero {n : PlanarSectorMeasure.Plane} (hn : n ≠ 0) :
    planePerp n ≠ 0 := by
  intro h
  apply hn
  have h0 := congrArg (fun z : PlanarSectorMeasure.Plane => z 0) h
  have h1 := congrArg (fun z : PlanarSectorMeasure.Plane => z 1) h
  ext i
  fin_cases i
  · simpa [planePerp] using h1
  · simpa [planePerp] using h0

theorem inner_planePerp (n : PlanarSectorMeasure.Plane) :
    ⟪n, planePerp n⟫_ℝ = 0 := by
  simp [planePerp, PiLp.inner_apply, Fin.sum_univ_two]
  ring

private theorem closed_signs_of_same_strict {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    (h : decide (r < 0) = decide (s < 0)) :
    (r ≤ 0 ↔ s ≤ 0) ∧ (0 ≤ r ↔ 0 ≤ s) := by
  have hlt : r < 0 ↔ s < 0 := by simpa using h
  constructor
  · simpa [lt_iff_le_and_ne, hr, hs] using hlt
  · simpa only [not_lt] using not_congr hlt

/-- A sign-determined actual ambient cone whose active normals use at most
two orthogonal planar axes has a positive quarter-turn mass whenever a
strict active-sign witness exists. The witness is a vector, not a measure
or sector certificate. -/
theorem SignDetermined.volume_transverse_pos_quarters
    {N : Finset (Space m)} {C : Set (Space m)}
    (hC : SignDetermined N C) (p q : Space m)
    (hpq : LinearIndependent ℝ ![p, q])
    (hspan : ∀ n ∈ N, n ∈ normalSpan p q)
    (b c : PlanarSectorMeasure.Plane) (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : ⟪b, c⟫_ℝ = 0)
    (haxes : ∀ n (hn : n ∈ N), normal p q hpq n (hspan n hn) = b ∨
      normal p q hpq n (hspan n hn) = c)
    (hwitness : ∃ v ∈ normalSpan p q, v ∈ C ∧ ∀ n ∈ N, ⟪n, v⟫_ℝ ≠ 0) :
    ∃ k : ℕ, 0 < k ∧
      volume {θ | lift p q hpq (direction θ) ∈ C} =
        ENNReal.ofReal ((k : ℝ) * (Real.pi / 2)) := by
  classical
  let P : Bool × Bool → Prop := fun s => ∃ z : PlanarSectorMeasure.Plane,
    lift p q hpq z ∈ C ∧ (∀ n ∈ N, ⟪n, lift p q hpq z⟫_ℝ ≠ 0) ∧
      (decide (⟪b, z⟫_ℝ < 0), decide (⟪c, z⟫_ℝ < 0)) = s
  let Q : Finset (Bool × Bool) := Finset.univ.filter P
  have hQ : Q.Nonempty := by
    obtain ⟨v, hvspan, hvC, hvsign⟩ := hwitness
    let z := normal p q hpq v hvspan
    refine ⟨(decide (⟪b, z⟫_ℝ < 0), decide (⟪c, z⟫_ℝ < 0)), ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, z, ?_, ?_, rfl⟩
    · simpa [z] using hvC
    · simpa [z] using hvsign
  refine ⟨Q.card, Finset.card_pos.mpr hQ, ?_⟩
  have heq : {θ | lift p q hpq (direction θ) ∈ C} =ᵐ[volume]
      booleanSignSector b c P := by
    apply ae_iff.mpr
    apply measure_mono_null
      (t := {θ | ⟪b, direction θ⟫_ℝ = 0} ∪ {θ | ⟪c, direction θ⟫_ℝ = 0}) _
      (measure_union_null (volume_normal_boundary hb) (volume_normal_boundary hc))
    intro θ hθ
    by_contra haxis
    have hbθ : ⟪b, direction θ⟫_ℝ ≠ 0 := fun h => haxis (Or.inl h)
    have hcθ : ⟪c, direction θ⟫_ℝ ≠ 0 := fun h => haxis (Or.inr h)
    have hNθ : ∀ n ∈ N, ⟪n, lift p q hpq (direction θ)⟫_ℝ ≠ 0 := by
      intro n hn
      rw [inner_normal_lift p q hpq n (hspan n hn)]
      rcases haxes n hn with h | h
      · rwa [h]
      · rwa [h]
    apply hθ
    apply propext
    change (lift p q hpq (direction θ) ∈ C) ↔
      P (decide (⟪b, direction θ⟫_ℝ < 0), decide (⟪c, direction θ⟫_ℝ < 0))
    constructor
    · intro hmem
      exact ⟨direction θ, hmem, hNθ, rfl⟩
    · rintro ⟨z, hzC, hzsign, hz⟩
      apply (hC _ _ ?_).mp hzC
      intro n hn
      apply closed_signs_of_same_strict (hzsign n hn) (hNθ n hn)
      simp only [inner_normal_lift p q hpq n (hspan n hn)]
      rcases haxes n hn with h | h
      · rw [h]
        exact congrArg Prod.fst hz
      · rw [h]
        exact congrArg Prod.snd hz
  rw [measure_congr heq]
  exact volume_booleanSignSector hb hc hbc P

/-- Construct two nonzero orthogonal axes for an actual nonempty family of
at most two active normals. In the singleton case the second axis is the
explicit perpendicular, in the same constructed root-normal plane. -/
theorem exists_orthogonal_planar_axes (N : Finset (Space m))
    (hne : N.Nonempty) (hcard : N.card ≤ 2)
    (hnz : ∀ n ∈ N, n ≠ 0)
    (horth : ∀ n ∈ N, ∀ w ∈ N, n ≠ w → ⟪n, w⟫_ℝ = 0)
    (p q : Space m) (hpq : LinearIndependent ℝ ![p, q])
    (hspan : ∀ n ∈ N, n ∈ normalSpan p q) :
    ∃ b c : PlanarSectorMeasure.Plane, b ≠ 0 ∧ c ≠ 0 ∧ ⟪b, c⟫_ℝ = 0 ∧
      ∀ n (hn : n ∈ N), normal p q hpq n (hspan n hn) = b ∨
        normal p q hpq n (hspan n hn) = c := by
  classical
  by_cases htwo : N.card = 2
  · obtain ⟨n, w, hnw, hN⟩ := Finset.card_eq_two.mp htwo
    have hn : n ∈ N := by simp [hN]
    have hw : w ∈ N := by simp [hN]
    refine ⟨normal p q hpq n (hspan n hn), normal p q hpq w (hspan w hw),
      ?_, ?_, ?_, ?_⟩
    · simpa using hnz n hn
    · simpa using hnz w hw
    · simpa using horth n hn w hw hnw
    · intro u hu
      have hu' : u = n ∨ u = w := by simpa [hN] using hu
      rcases hu' with rfl | rfl <;> simp
  · have hone : N.card = 1 := by have := Finset.card_pos.mpr hne; omega
    obtain ⟨n, hN⟩ := Finset.card_eq_one.mp hone
    have hn : n ∈ N := by simp [hN]
    let b := normal p q hpq n (hspan n hn)
    have hb : b ≠ 0 := by simpa [b] using hnz n hn
    refine ⟨b, planePerp b, hb, planePerp_ne_zero hb, inner_planePerp b, ?_⟩
    intro u hu
    have hu' : u = n := by simpa [hN] using hu
    subst u
    exact Or.inl rfl

/-- The actual ordinary incident carrier cone has a positive natural multiple
of a quarter-turn as its angular mass in any root-normal chart. No angular
mass, positivity, sign-sector representation, or regularity certificate is
an input. The normals and cone are the literal native carrier formulas. -/
theorem placedCarrierCone_volume_pos_quarters
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients polyCells J)
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hpq : LinearIndependent ℝ ![p, q])
    (hx : f.symm x ∈ frontier (body a))
    (hkey : ∀ u, f.symm x ∉ keyGraph a u)
    (hcard : (placedActiveCarrierNormals polyCells f x).card ≤ 2)
    (hspan : ∀ n ∈ placedActiveCarrierNormals polyCells f x,
      n ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    ∃ k : ℕ, 0 < k ∧
      volume {θ | lift p q hpq (direction θ) ∈ placedCarrierCone polyCells f x} =
        ENNReal.ofReal ((k : ℝ) * (Real.pi / 2)) := by
  obtain ⟨b, c, hb, hc, hbc, haxes⟩ := exists_orthogonal_planar_axes
    (placedActiveCarrierNormals polyCells f x) (placedActiveCarrierNormals_nonempty hm a f x hx hkey)
    hcard (placedActiveCarrierNormals_ne_zero polyCells f x)
    (placedActiveCarrierNormals_pairwise_orthogonal polyCells f x) p q hpq hspan
  apply (placedCarrierCone_signDetermined polyCells f x).volume_transverse_pos_quarters
    p q hpq hspan b c hb hc hbc haxes
  obtain ⟨v, hvspan, _, hvcone, hvsign⟩ :=
    placedCarrierCone_strict_inward_direction hm a f x p q hx hkey hspan
  exact ⟨v, hvspan, hvcone, hvsign⟩

/-- The same actual ordinary mass formula from the boundary-plane control
used to construct the conical fan; the at-most-two bound is proved internally. -/
theorem placedCarrierCone_volume_pos_quarters_of_boundary_span
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients polyCells J)
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hpq : LinearIndependent ℝ ![p, q])
    (hx : f.symm x ∈ frontier (body a))
    (hkey : ∀ u, f.symm x ∉ keyGraph a u)
    (hplanes : ∀ b : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a b →
      placedNormal f (boundaryPlaneNormal a b) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    ∃ k : ℕ, 0 < k ∧
      volume {θ | lift p q hpq (direction θ) ∈ placedCarrierCone polyCells f x} =
        ENNReal.ofReal ((k : ℝ) * (Real.pi / 2)) := by
  obtain ⟨hcard, hspan⟩ := placedActiveCarrierNormals_span_card a f x p q hplanes
  exact placedCarrierCone_volume_pos_quarters hm a f x p q hpq hx hkey hcard hspan

/-- Real-valued form of the derived ordinary angular mass. -/
theorem placedCarrierCone_angle_pos_quarters
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients polyCells J)
    (f : Space m ≃ᵢ Space m) (x p q : Space m)
    (hpq : LinearIndependent ℝ ![p, q])
    (hx : f.symm x ∈ frontier (body a))
    (hkey : ∀ u, f.symm x ∉ keyGraph a u)
    (hcard : (placedActiveCarrierNormals polyCells f x).card ≤ 2)
    (hspan : ∀ n ∈ placedActiveCarrierNormals polyCells f x,
      n ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    ∃ k : ℕ, 0 < k ∧
      (volume {θ | lift p q hpq (direction θ) ∈ placedCarrierCone polyCells f x}).toReal =
        (k : ℝ) * (Real.pi / 2) := by
  obtain ⟨k, hk, hmass⟩ :=
    placedCarrierCone_volume_pos_quarters hm a f x p q hpq hx hkey hcard hspan
  refine ⟨k, hk, ?_⟩
  rw [hmass, ENNReal.toReal_ofReal (by positivity)]

#print axioms SignDetermined.volume_transverse_pos_quarters
#print axioms exists_orthogonal_planar_axes
#print axioms placedCarrierCone_volume_pos_quarters
#print axioms placedCarrierCone_volume_pos_quarters_of_boundary_span
#print axioms placedCarrierCone_angle_pos_quarters

end
end ProductClosure.NativeCompiler
