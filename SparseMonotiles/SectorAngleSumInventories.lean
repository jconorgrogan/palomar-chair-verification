module

public import SparseMonotiles.SectorAngleSumPlaneGeometry
public import SparseMonotiles.SectorArithmetic
public import SparseMonotiles.CanonicalRidgeNormals

@[expose] public section

/-! # Certified sector inventories from actual normal angles -/

namespace SparseMonotiles
namespace SectorAngleSum

open Set InnerProductGeometry
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine half-plane is an allowed flat sector. -/
theorem halfplane_angle_inventory (n : E) (hn : n ≠ 0) :
    HasSectorAngle (normalHalfspace n) Real.pi ∧
      SectorArithmetic.InAngleInventory Real.pi :=
  ⟨.halfplane n hn rfl, Or.inr (Or.inl rfl)⟩

/-- A small actual inward-normal angle yields precisely the allowed convex
and reflex key-crease angles. -/
theorem small_normal_angle_inventory (n m : E) (hn : n ≠ 0) (hm : m ≠ 0)
    (ha0 : 0 < angle n m) (ha : angle n m < Real.pi/4) :
    (HasSectorAngle (normalHalfspace n ∩ normalHalfspace m) (Real.pi-angle n m) ∧
      SectorArithmetic.InAngleInventory (Real.pi-angle n m)) ∧
    (HasSectorAngle (normalHalfspace n ∪ normalHalfspace m) (Real.pi+angle n m) ∧
      SectorArithmetic.InAngleInventory (Real.pi+angle n m)) := by
  have hpi : angle n m < Real.pi := by linarith [Real.pi_pos]
  exact ⟨⟨.convex n m hn hm hpi rfl,
      Or.inr (Or.inr (Or.inr ⟨angle n m,ha0,ha,Or.inl rfl⟩))⟩,
    ⟨.reflex n m hn hm hpi rfl,
      Or.inr (Or.inr (Or.inr ⟨angle n m,ha0,ha,Or.inr rfl⟩))⟩⟩

/-- Orthogonal inward normals give precisely a quadrant and a reflex quadrant. -/
theorem orthogonal_normal_angle_inventory (n m : E) (hn : n ≠ 0) (hm : m ≠ 0)
    (horth : ⟪n,m⟫_ℝ = 0) :
    (HasSectorAngle (normalHalfspace n ∩ normalHalfspace m) (Real.pi/2) ∧
      SectorArithmetic.InAngleInventory (Real.pi/2)) ∧
    (HasSectorAngle (normalHalfspace n ∪ normalHalfspace m) (3*Real.pi/2) ∧
      SectorArithmetic.InAngleInventory (3*Real.pi/2)) := by
  have he : angle n m = Real.pi/2 := (inner_eq_zero_iff_angle_eq_pi_div_two n m).mp horth
  have hl : angle n m < Real.pi := by rw [he]; linarith [Real.pi_pos]
  have hc := HasSectorAngle.convex n m hn hm hl rfl
  have hr := HasSectorAngle.reflex n m hn hm hl rfl
  rw [he, show Real.pi-Real.pi/2 = Real.pi/2 by ring] at hc
  rw [he, show Real.pi+Real.pi/2 = 3*Real.pi/2 by ring] at hr
  exact ⟨⟨hc,Or.inl rfl⟩,⟨hr,Or.inr (Or.inr (Or.inl rfl))⟩⟩

/-- The canonical base-side deviation is the genuine angle of the inward
normals for its reflex bump wedge. -/
theorem base_side_inward_angle {n : ℕ} (i : Fin n) (b : Bool) (s : ℝ) (hs : 0 ≤ s) :
    angle (-pyramidBaseNormal n) (pyramidSlopeNormal i b s) = baseCreaseDeviation s := by
  rw [angle, inner_neg_left, norm_neg]
  exact base_slope_normal_deviation i b s hs

/-- Reversing both inward normals preserves the actual crease angle. -/
theorem base_side_dent_inward_angle {n : ℕ} (i : Fin n) (b : Bool) (s : ℝ) (hs : 0 ≤ s) :
    angle (pyramidBaseNormal n) (-pyramidSlopeNormal i b s) = baseCreaseDeviation s := by
  rw [angle, inner_neg_right, norm_neg]
  exact base_slope_normal_deviation i b s hs

/-- The canonical distinct-side deviation is its genuine inward-normal angle. -/
theorem side_side_inward_angle {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (b c : Bool) (s t : ℝ) :
    angle (pyramidSlopeNormal i b s) (pyramidSlopeNormal j c t) = sideCreaseDeviation s t :=
  distinct_slope_normal_deviation i j hij b c s t

/-- Negating both side normals, as required by a dent, preserves that angle. -/
theorem side_side_dent_inward_angle {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (b c : Bool) (s t : ℝ) :
    angle (-pyramidSlopeNormal i b s) (-pyramidSlopeNormal j c t) = sideCreaseDeviation s t := by
  rw [angle, inner_neg_neg, norm_neg, norm_neg]
  exact distinct_slope_normal_deviation i j hij b c s t

#print axioms small_normal_angle_inventory
#print axioms orthogonal_normal_angle_inventory
#print axioms base_side_inward_angle
#print axioms side_side_inward_angle

end SectorAngleSum
end SparseMonotiles
