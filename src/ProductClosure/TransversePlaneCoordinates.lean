module

public import PhysicalRegistration.TransversePlaneCoordinates
public import ProductClosure.CreasePlaneGerms

@[expose] public section
namespace ProductClosure.NativeCompiler
open PhysicalRegistration.TransversePlaneCoordinates
noncomputable section
open PhysicalRegistration
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- The literal native base-crease normal plane. -/
def baseNormalSpan {J : ℕ} (a : Coefficients polyCells J) (u : Site polyCells) (s : Side m) :
    Submodule ℝ (Space m) := normalSpan (outward u.1) (sideNormal a u s)

/-- The literal native side-crease normal plane. -/
def sideNormalSpan {J : ℕ} (a : Coefficients polyCells J) (u : Site polyCells) (s t : Side m) :
    Submodule ℝ (Space m) := normalSpan (sideNormal a u s) (sideNormal a u t)

theorem finrank_baseNormalSpan {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s : Side m) : Module.finrank ℝ (baseNormalSpan a u s) = 2 :=
  finrank_normalSpan _ _ (base_normals_linearIndependent a u s)

theorem finrank_sideNormalSpan {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1) :
    Module.finrank ℝ (sideNormalSpan a u s t) = 2 :=
  finrank_normalSpan _ _ (side_normals_linearIndependent a u s t hst)

/-- The actual native base-crease planar isometry. -/
def baseTransverseCoordinates {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s : Side m) : baseNormalSpan a u s ≃ₗᵢ[ℝ] Plane :=
  coordinates _ _ (base_normals_linearIndependent a u s)

/-- The actual native distinct-axis side-crease planar isometry. -/
def sideTransverseCoordinates {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1) :
    sideNormalSpan a u s t ≃ₗᵢ[ℝ] Plane :=
  coordinates _ _ (side_normals_linearIndependent a u s t hst)

/-- Base-crease normal span after an arbitrary ambient placement. -/
def placedBaseNormalSpan {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s : Side m) (f : Space m ≃ᵢ Space m) : Submodule ℝ (Space m) :=
  normalSpan (placedNormal f (outward u.1)) (placedNormal f (sideNormal a u s))

/-- Side-crease normal span after an arbitrary ambient placement. -/
def placedSideNormalSpan {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s t : Side m) (f : Space m ≃ᵢ Space m) : Submodule ℝ (Space m) :=
  normalSpan (placedNormal f (sideNormal a u s)) (placedNormal f (sideNormal a u t))

theorem placed_base_normals_linearIndependent {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s : Side m) (f : Space m ≃ᵢ Space m) :
    LinearIndependent ℝ ![placedNormal f (outward u.1), placedNormal f (sideNormal a u s)] :=
  independent_map f.toRealAffineIsometryEquiv.linearIsometryEquiv _ _
    (base_normals_linearIndependent a u s)

theorem placed_side_normals_linearIndependent {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1) (f : Space m ≃ᵢ Space m) :
    LinearIndependent ℝ ![placedNormal f (sideNormal a u s), placedNormal f (sideNormal a u t)] :=
  independent_map f.toRealAffineIsometryEquiv.linearIsometryEquiv _ _
    (side_normals_linearIndependent a u s t hst)

theorem finrank_placedBaseNormalSpan {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s : Side m) (f : Space m ≃ᵢ Space m) :
    Module.finrank ℝ (placedBaseNormalSpan a u s f) = 2 :=
  finrank_normalSpan _ _ (placed_base_normals_linearIndependent a u s f)

theorem finrank_placedSideNormalSpan {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1) (f : Space m ≃ᵢ Space m) :
    Module.finrank ℝ (placedSideNormalSpan a u s t f) = 2 :=
  finrank_normalSpan _ _ (placed_side_normals_linearIndependent a u s t hst f)

/-- A planar chart for every placed base crease, including all rotations,
reflections and translations. -/
def placedBaseTransverseCoordinates {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s : Side m) (f : Space m ≃ᵢ Space m) :
    placedBaseNormalSpan a u s f ≃ₗᵢ[ℝ] Plane :=
  coordinates _ _ (placed_base_normals_linearIndependent a u s f)

/-- A planar chart for every placed distinct-axis side crease. -/
def placedSideTransverseCoordinates {J : ℕ} (a : Coefficients polyCells J)
    (u : Site polyCells) (s t : Side m) (hst : s.1 ≠ t.1) (f : Space m ≃ᵢ Space m) :
    placedSideNormalSpan a u s t f ≃ₗᵢ[ℝ] Plane :=
  coordinates _ _ (placed_side_normals_linearIndependent a u s t hst f)


end
end ProductClosure.NativeCompiler
