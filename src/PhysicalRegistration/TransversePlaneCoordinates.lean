module

public import PhysicalRegistration.CreasePlaneGerms
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

@[expose] public section

/-!
# Isometric coordinates on actual crease-normal planes

The two-dimensional rank is proved from the literal native normals. An
orthonormal basis of their span, reindexed using this rank equality, constructs
an actual linear isometry equivalence to `EuclideanSpace ℝ (Fin 2)`. The same
construction applies after every ambient isometric bijection. The restriction
lemmas identify ambient homogeneous inequalities and angles with their planar
counterparts; no transverse chart or rank certificate is assumed at a native
or placed endpoint.
-/

namespace PhysicalRegistration.TransversePlaneCoordinates
open scoped InnerProductSpace
open Set
noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual span of the two defining normals. -/
def normalSpan (p q : E) : Submodule ℝ E := Submodule.span ℝ {p, q}

@[simp] theorem left_mem_normalSpan (p q : E) : p ∈ normalSpan p q :=
  Submodule.subset_span (by simp)

@[simp] theorem right_mem_normalSpan (p q : E) : q ∈ normalSpan p q :=
  Submodule.subset_span (by simp)

instance normalSpan_finiteDimensional (p q : E) :
    FiniteDimensional ℝ (normalSpan p q) :=
  FiniteDimensional.span_of_finite ℝ (Set.toFinite {p, q})

/-- Independence computes the dimension; it is not a field of a chart record. -/
theorem finrank_normalSpan (p q : E) (h : LinearIndependent ℝ ![p, q]) :
    Module.finrank ℝ (normalSpan p q) = 2 := by
  have hr : Set.range ![p, q] = {p, q} := by
    ext x
    simp [or_comm]
  have hd := finrank_span_eq_card h
  rw [hr] at hd
  change Module.finrank ℝ (Submodule.span ℝ {p, q}) = 2
  convert hd using 1
  norm_num

/-- A genuine orthonormal coordinate chart on the two-normal span. -/
def coordinates (p q : E) (h : LinearIndependent ℝ ![p, q]) :
    normalSpan p q ≃ₗᵢ[ℝ] Plane :=
  ((stdOrthonormalBasis ℝ (normalSpan p q)).reindex
    (finCongr (finrank_normalSpan p q h))).repr

/-- The corresponding isometric inclusion of the coordinate plane into the
ambient space. Its range is the actual two-normal span. -/
def lift (p q : E) (h : LinearIndependent ℝ ![p, q]) : Plane →ₗᵢ[ℝ] E :=
  (normalSpan p q).subtypeₗᵢ.comp (coordinates p q h).symm.toLinearIsometry

/-- A normal in the actual span, expressed in the constructed coordinates. -/
def normal (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n : E) (hn : n ∈ normalSpan p q) : Plane :=
  coordinates p q h ⟨n, hn⟩

@[simp] theorem lift_normal (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n : E) (hn : n ∈ normalSpan p q) :
    lift p q h (normal p q h n hn) = n := by
  simp [lift, normal]

@[simp] theorem lift_mem (p q : E) (h : LinearIndependent ℝ ![p, q]) (z : Plane) :
    lift p q h z ∈ normalSpan p q :=
  ((coordinates p q h).symm z).property

@[simp] theorem range_lift (p q : E) (h : LinearIndependent ℝ ![p, q]) :
    Set.range (lift p q h) = (normalSpan p q : Set E) := by
  ext n
  constructor
  · rintro ⟨z, rfl⟩
    exact lift_mem p q h z
  · intro hn
    exact ⟨normal p q h n hn, lift_normal p q h n hn⟩

@[simp] theorem norm_normal (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n : E) (hn : n ∈ normalSpan p q) :
    ‖normal p q h n hn‖ = ‖n‖ :=
  (coordinates p q h).norm_map ⟨n, hn⟩

@[simp] theorem normal_eq_zero_iff (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n : E) (hn : n ∈ normalSpan p q) :
    normal p q h n hn = 0 ↔ n = 0 := by
  change coordinates p q h ⟨n, hn⟩ = 0 ↔ n = 0
  rw [(coordinates p q h).map_eq_zero_iff]
  exact Subtype.ext_iff

@[simp] theorem inner_normal (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n w : E) (hn : n ∈ normalSpan p q) (hw : w ∈ normalSpan p q) :
    ⟪normal p q h n hn, normal p q h w hw⟫_ℝ = ⟪n, w⟫_ℝ :=
  (coordinates p q h).inner_map_map ⟨n, hn⟩ ⟨w, hw⟩

@[simp] theorem angle_normal (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n w : E) (hn : n ∈ normalSpan p q) (hw : w ∈ normalSpan p q) :
    InnerProductGeometry.angle (normal p q h n hn) (normal p q h w hw) =
      InnerProductGeometry.angle n w := by
  exact ((coordinates p q h).toLinearIsometry.angle_map ⟨n, hn⟩ ⟨w, hw⟩).trans
    (Submodule.angle_coe ⟨n, hn⟩ ⟨w, hw⟩).symm

/-- The prime-separation invariant is also unchanged by the planar chart. -/
@[simp] theorem normalCosSq_normal (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n w : E) (hn : n ∈ normalSpan p q) (hw : w ∈ normalSpan p q) :
    NativeChair.normalCosSq (normal p q h n hn) (normal p q h w hw) =
      NativeChair.normalCosSq n w := by
  simp only [NativeChair.normalCosSq, inner_normal]

/-- In particular, a genuinely independent pair of incident normals stays
independent when passed to the planar sector-measure lemmas. -/
theorem normal_linearIndependent (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n w : E) (hn : n ∈ normalSpan p q) (hw : w ∈ normalSpan p q)
    (hnw : LinearIndependent ℝ ![n, w]) :
    LinearIndependent ℝ ![normal p q h n hn, normal p q h w hw] := by
  apply LinearIndependent.of_comp (lift p q h).toLinearMap
  convert hnw using 1
  funext i
  fin_cases i <;> simp

/-- The exact scalar identity needed to restrict every ambient homogeneous
cone inequality to the transverse coordinate plane. -/
theorem inner_normal_lift (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n : E) (hn : n ∈ normalSpan p q) (z : Plane) :
    ⟪n, lift p q h z⟫_ℝ = ⟪normal p q h n hn, z⟫_ℝ := by
  have he := (lift p q h).inner_map_map (normal p q h n hn) z
  simpa only [lift_normal] using he

/-- Closed halfspaces restrict exactly, with no sign or scale change. -/
theorem halfspace_preimage (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n : E) (hn : n ∈ normalSpan p q) :
    lift p q h ⁻¹' {v : E | ⟪n, v⟫_ℝ ≤ 0} =
      {z : Plane | ⟪normal p q h n hn, z⟫_ℝ ≤ 0} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [inner_normal_lift p q h n hn]

/-- Strict halfspaces restrict by the same scalar identity. -/
theorem strictHalfspace_preimage (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n : E) (hn : n ∈ normalSpan p q) :
    lift p q h ⁻¹' {v : E | ⟪n, v⟫_ℝ < 0} =
      {z : Plane | ⟪normal p q h n hn, z⟫_ℝ < 0} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [inner_normal_lift p q h n hn]

/-- Arbitrary families of simultaneous homogeneous inequalities restrict
exactly. Finite polyhedral material cones are a special case. -/
theorem cone_preimage {ι : Type*} (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n : ι → E) (hn : ∀ i, n i ∈ normalSpan p q) :
    lift p q h ⁻¹' {v : E | ∀ i, ⟪n i, v⟫_ℝ ≤ 0} =
      {z : Plane | ∀ i, ⟪normal p q h (n i) (hn i), z⟫_ℝ ≤ 0} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  simp_rw [inner_normal_lift p q h _ (hn _)]

/-- The same restriction for reentrant material cones described by unions. -/
theorem unionCone_preimage {ι : Type*} (p q : E) (h : LinearIndependent ℝ ![p, q])
    (n : ι → E) (hn : ∀ i, n i ∈ normalSpan p q) :
    lift p q h ⁻¹' {v : E | ∃ i, ⟪n i, v⟫_ℝ ≤ 0} =
      {z : Plane | ∃ i, ⟪normal p q h (n i) (hn i), z⟫_ℝ ≤ 0} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  simp_rw [inner_normal_lift p q h _ (hn _)]

/-- Independence survives every injective isometric linear placement. -/
theorem independent_map (L : E ≃ₗᵢ[ℝ] E) (p q : E)
    (h : LinearIndependent ℝ ![p, q]) : LinearIndependent ℝ ![L p, L q] := by
  have hmap := h.map' L.toLinearEquiv.toLinearMap
    (LinearMap.ker_eq_bot.mpr L.injective)
  convert hmap using 1
  funext i
  fin_cases i <;> rfl

end
end PhysicalRegistration.TransversePlaneCoordinates

namespace PhysicalRegistration.NativeChair
open TransversePlaneCoordinates
noncomputable section

/-- The literal native base-crease normal plane. -/
def baseNormalSpan {m J : ℕ} (a : Coefficients m J) (u : Site m) (s : Side m) :
    Submodule ℝ (Space m) := normalSpan (outward u.1) (sideNormal a u s)

/-- The literal native side-crease normal plane. -/
def sideNormalSpan {m J : ℕ} (a : Coefficients m J) (u : Site m) (s t : Side m) :
    Submodule ℝ (Space m) := normalSpan (sideNormal a u s) (sideNormal a u t)

theorem finrank_baseNormalSpan {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s : Side m) : Module.finrank ℝ (baseNormalSpan a u s) = 2 :=
  finrank_normalSpan _ _ (base_normals_linearIndependent a u s)

theorem finrank_sideNormalSpan {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    Module.finrank ℝ (sideNormalSpan a u s t) = 2 :=
  finrank_normalSpan _ _ (side_normals_linearIndependent a u s t hst)

/-- The actual native base-crease planar isometry. -/
def baseTransverseCoordinates {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s : Side m) : baseNormalSpan a u s ≃ₗᵢ[ℝ] Plane :=
  coordinates _ _ (base_normals_linearIndependent a u s)

/-- The actual native distinct-axis side-crease planar isometry. -/
def sideTransverseCoordinates {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) :
    sideNormalSpan a u s t ≃ₗᵢ[ℝ] Plane :=
  coordinates _ _ (side_normals_linearIndependent a u s t hst)

/-- Base-crease normal span after an arbitrary ambient placement. -/
def placedBaseNormalSpan {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s : Side m) (f : Space m ≃ᵢ Space m) : Submodule ℝ (Space m) :=
  normalSpan (placedNormal f (outward u.1)) (placedNormal f (sideNormal a u s))

/-- Side-crease normal span after an arbitrary ambient placement. -/
def placedSideNormalSpan {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s t : Side m) (f : Space m ≃ᵢ Space m) : Submodule ℝ (Space m) :=
  normalSpan (placedNormal f (sideNormal a u s)) (placedNormal f (sideNormal a u t))

theorem placed_base_normals_linearIndependent {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s : Side m) (f : Space m ≃ᵢ Space m) :
    LinearIndependent ℝ ![placedNormal f (outward u.1), placedNormal f (sideNormal a u s)] :=
  independent_map f.toRealAffineIsometryEquiv.linearIsometryEquiv _ _
    (base_normals_linearIndependent a u s)

theorem placed_side_normals_linearIndependent {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) (f : Space m ≃ᵢ Space m) :
    LinearIndependent ℝ ![placedNormal f (sideNormal a u s), placedNormal f (sideNormal a u t)] :=
  independent_map f.toRealAffineIsometryEquiv.linearIsometryEquiv _ _
    (side_normals_linearIndependent a u s t hst)

theorem finrank_placedBaseNormalSpan {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s : Side m) (f : Space m ≃ᵢ Space m) :
    Module.finrank ℝ (placedBaseNormalSpan a u s f) = 2 :=
  finrank_normalSpan _ _ (placed_base_normals_linearIndependent a u s f)

theorem finrank_placedSideNormalSpan {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) (f : Space m ≃ᵢ Space m) :
    Module.finrank ℝ (placedSideNormalSpan a u s t f) = 2 :=
  finrank_normalSpan _ _ (placed_side_normals_linearIndependent a u s t hst f)

/-- A planar chart for every placed base crease, including all rotations,
reflections and translations. -/
def placedBaseTransverseCoordinates {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s : Side m) (f : Space m ≃ᵢ Space m) :
    placedBaseNormalSpan a u s f ≃ₗᵢ[ℝ] Plane :=
  coordinates _ _ (placed_base_normals_linearIndependent a u s f)

/-- A planar chart for every placed distinct-axis side crease. -/
def placedSideTransverseCoordinates {m J : ℕ} (a : Coefficients m J)
    (u : Site m) (s t : Side m) (hst : s.1 ≠ t.1) (f : Space m ≃ᵢ Space m) :
    placedSideNormalSpan a u s t f ≃ₗᵢ[ℝ] Plane :=
  coordinates _ _ (placed_side_normals_linearIndependent a u s t hst f)

#print axioms finrank_baseNormalSpan
#print axioms finrank_sideNormalSpan
#print axioms baseTransverseCoordinates
#print axioms sideTransverseCoordinates
#print axioms finrank_placedBaseNormalSpan
#print axioms finrank_placedSideNormalSpan
#print axioms placedBaseTransverseCoordinates
#print axioms placedSideTransverseCoordinates
#print axioms TransversePlaneCoordinates.normalCosSq_normal
#print axioms TransversePlaneCoordinates.normal_linearIndependent
#print axioms TransversePlaneCoordinates.inner_normal_lift
#print axioms TransversePlaneCoordinates.angle_normal
#print axioms TransversePlaneCoordinates.cone_preimage
#print axioms TransversePlaneCoordinates.unionCone_preimage

end
end PhysicalRegistration.NativeChair
