module

public import SparseMonotiles.Constants
public import SparseMonotiles.KeyCovariance

@[expose] public section

/-!
# Exact reference pyramids and their physical Euclidean binding

The reference keys lie on the last-coordinate-zero unit facet. Their base
centres are the facet centre plus the prescribed tangential displacement.
Integer coordinates are decoded with the same denominators as the exact
five- and seven-dimensional key data. The contact convention reverses the
coefficient in `Pose.boxKey`; it does not reverse a physical bump under a
Euclidean isometry. The solid and base themselves ignore the coefficient.
-/
namespace SparseMonotiles.Canonical

open Contact

/-- Extensionality for exact rational key data, with all coordinates explicit. -/
theorem keyData_ext_of_coordinates {d : ℕ} (a b : KeyData d)
    (hc : ∀ i, a.centre i = b.centre i)
    (hr : ∀ i, a.radius i = b.radius i)
    (ha : ∀ i, a.apex i = b.apex i)
    (hb : a.bump = b.bump) : a = b := by
  cases a
  cases b
  simp only [KeyData.mk.injEq]
  exact ⟨funext hc, funext hr, funext ha, hb⟩

/-- Denominator-cleared reference key in dimension five. -/
def referenceBox5 (b : Bool) : BoxKey 5 where
  centre := ![10560, 11520, 12480, 13440, 0]
  radius := ![240, 300, 360, 420, 0]
  apex := ![10640, 11595, 12552, 13510, 80]
  bump := b

/-- Denominator-cleared reference key in dimension seven. -/
def referenceBox7 (b : Bool) : BoxKey 7 where
  centre := ![100800, 107520, 114240, 120960, 127680, 134400, 0]
  radius := ![1680, 1960, 2240, 2520, 2800, 3080, 0]
  apex := ![101360, 108010, 114688, 121380, 128080, 134785, 560]
  bump := b

/-- Actual closed Euclidean reference solid for the five-dimensional keys. -/
def referenceSolid5 : Set (Point 5) :=
  keySolid ((referenceBox5 true).toKeyData 19200)

/-- Actual closed Euclidean reference solid for the seven-dimensional keys. -/
def referenceSolid7 : Set (Point 7) :=
  keySolid ((referenceBox7 true).toKeyData 188160)

@[simp] theorem referenceBox5_bump (b : Bool) : (referenceBox5 b).bump = b := rfl
@[simp] theorem referenceBox7_bump (b : Bool) : (referenceBox7 b).bump = b := rfl

/-- The tag selects a union in `body`, not the geometry of this one pyramid. -/
@[simp] theorem referenceBox5_keySolid (b : Bool) :
    keySolid ((referenceBox5 b).toKeyData 19200) = referenceSolid5 := rfl

@[simp] theorem referenceBox7_keySolid (b : Bool) :
    keySolid ((referenceBox7 b).toKeyData 188160) = referenceSolid7 := rfl

theorem referenceBox5_keyBase_independent (b c : Bool) :
    keyBase ((referenceBox5 b).toKeyData 19200) =
      keyBase ((referenceBox5 c).toKeyData 19200) := rfl

theorem referenceBox7_keyBase_independent (b c : Bool) :
    keyBase ((referenceBox7 b).toKeyData 188160) =
      keyBase ((referenceBox7 c).toKeyData 188160) := rfl

/-- A checked integer pose certificate binds the exact five-dimensional solid.
The reversed input coefficient is only the opposed-normal contact convention. -/
theorem canonical5_of_box_match (p : Pose 5) {box : BoxKey 5} {k : KeyData 5}
    (hbox : p.boxKey 19200 (referenceBox5 (!box.bump)) = box)
    (hk : box.toKeyData 19200 = k) :
    keySolid k = p.euclidean '' referenceSolid5 := by
  calc
    keySolid k = keySolid ((p.boxKey 19200 (referenceBox5 (!box.bump))).toKeyData 19200) :=
      by rw [hbox, hk]
    _ = p.euclidean '' keySolid ((referenceBox5 (!box.bump)).toKeyData 19200) :=
      (p.boxKey_image_keySolid (by norm_num) _).symm
    _ = p.euclidean '' referenceSolid5 := by rw [referenceBox5_keySolid]

/-- A checked integer pose certificate binds the exact seven-dimensional solid. -/
theorem canonical7_of_box_match (p : Pose 7) {box : BoxKey 7} {k : KeyData 7}
    (hbox : p.boxKey 188160 (referenceBox7 (!box.bump)) = box)
    (hk : box.toKeyData 188160 = k) :
    keySolid k = p.euclidean '' referenceSolid7 := by
  calc
    keySolid k = keySolid ((p.boxKey 188160 (referenceBox7 (!box.bump))).toKeyData 188160) :=
      by rw [hbox, hk]
    _ = p.euclidean '' keySolid ((referenceBox7 (!box.bump)).toKeyData 188160) :=
      (p.boxKey_image_keySolid (by norm_num) _).symm
    _ = p.euclidean '' referenceSolid7 := by rw [referenceBox7_keySolid]

/-- The prescribed tangential displacement from the centre of the unit facet. -/
theorem referenceBox5_centre (b : Bool) (i : Fin 4) :
    ((referenceBox5 b).toKeyData 19200).centre i.castSucc =
      1/2 + ((i.val + 1 : ℕ) : ℚ) / 20 := by
  fin_cases i <;> norm_num [referenceBox5, BoxKey.toKeyData, rationalVertex]

theorem referenceBox7_centre (b : Bool) (i : Fin 6) :
    ((referenceBox7 b).toKeyData 188160).centre i.castSucc =
      1/2 + ((i.val + 1 : ℕ) : ℚ) / 28 := by
  fin_cases i <;> norm_num [referenceBox7, BoxKey.toKeyData, rationalVertex]

theorem referenceBox5_radius (b : Bool) (i : Fin 4) :
    ((referenceBox5 b).toKeyData 19200).radius i.castSucc = widths5 i := by
  fin_cases i <;> norm_num [referenceBox5, BoxKey.toKeyData, rationalVertex, widths5]

theorem referenceBox7_radius (b : Bool) (i : Fin 6) :
    ((referenceBox7 b).toKeyData 188160).radius i.castSucc = widths7 i := by
  fin_cases i <;> norm_num [referenceBox7, BoxKey.toKeyData, rationalVertex, widths7]

/-- The apex displacement, rather than its absolute coordinate, is the offset. -/
theorem referenceBox5_offset (b : Bool) (i : Fin 4) :
    ((referenceBox5 b).toKeyData 19200).apex i.castSucc -
      ((referenceBox5 b).toKeyData 19200).centre i.castSucc = offsets5 i := by
  fin_cases i <;> norm_num [referenceBox5, BoxKey.toKeyData, rationalVertex, offsets5]

theorem referenceBox7_offset (b : Bool) (i : Fin 6) :
    ((referenceBox7 b).toKeyData 188160).apex i.castSucc -
      ((referenceBox7 b).toKeyData 188160).centre i.castSucc = offsets7 i := by
  fin_cases i <;> norm_num [referenceBox7, BoxKey.toKeyData, rationalVertex, offsets7]

@[simp] theorem referenceBox5_normal_centre (b : Bool) :
    ((referenceBox5 b).toKeyData 19200).centre 4 = 0 := by
  change (0 : ℚ) / 19200 = 0
  norm_num

@[simp] theorem referenceBox7_normal_centre (b : Bool) :
    ((referenceBox7 b).toKeyData 188160).centre 6 = 0 := by
  change (0 : ℚ) / 188160 = 0
  norm_num

@[simp] theorem referenceBox5_normal_radius (b : Bool) :
    ((referenceBox5 b).toKeyData 19200).radius 4 = 0 := by
  change (0 : ℚ) / 19200 = 0
  norm_num

@[simp] theorem referenceBox7_normal_radius (b : Bool) :
    ((referenceBox7 b).toKeyData 188160).radius 6 = 0 := by
  change (0 : ℚ) / 188160 = 0
  norm_num

@[simp] theorem referenceBox5_height (b : Bool) :
    ((referenceBox5 b).toKeyData 19200).apex 4 = 1/240 := by
  change (80 : ℚ) / 19200 = 1/240
  norm_num

@[simp] theorem referenceBox7_height (b : Bool) :
    ((referenceBox7 b).toKeyData 188160).apex 6 = 1/336 := by
  change (560 : ℚ) / 188160 = 1/336
  norm_num

/-- Nondegenerate tangential widths are proved from the exact constants. -/
theorem referenceBox5_radius_pos (b : Bool) (i : Fin 4) :
    0 < ((referenceBox5 b).toKeyData 19200).radius i.castSucc := by
  rw [referenceBox5_radius]
  exact lt_trans (key5_offsets_inside i).1 (key5_offsets_inside i).2

theorem referenceBox7_radius_pos (b : Bool) (i : Fin 6) :
    0 < ((referenceBox7 b).toKeyData 188160).radius i.castSucc := by
  rw [referenceBox7_radius]
  exact lt_trans (key7_offsets_inside i).1 (key7_offsets_inside i).2

theorem referenceBox5_radius_nonneg (b : Bool) (i : Fin 5) :
    0 ≤ ((referenceBox5 b).toKeyData 19200).radius i := by
  fin_cases i <;> norm_num [referenceBox5, BoxKey.toKeyData, rationalVertex]

theorem referenceBox7_radius_nonneg (b : Bool) (i : Fin 7) :
    0 ≤ ((referenceBox7 b).toKeyData 188160).radius i := by
  fin_cases i <;> norm_num [referenceBox7, BoxKey.toKeyData, rationalVertex]

/-- The actual Euclidean base contains its decoded rational centre. -/
theorem referenceBox5_centre_mem_keyBase (b : Bool) :
    rationalPoint ((referenceBox5 b).toKeyData 19200).centre ∈
      keyBase ((referenceBox5 b).toKeyData 19200) := by
  intro i
  change |(((referenceBox5 b).toKeyData 19200).centre i : ℝ) -
    (((referenceBox5 b).toKeyData 19200).centre i : ℝ)| ≤ _
  rw [sub_self, abs_zero]
  exact_mod_cast referenceBox5_radius_nonneg b i

theorem referenceBox7_centre_mem_keyBase (b : Bool) :
    rationalPoint ((referenceBox7 b).toKeyData 188160).centre ∈
      keyBase ((referenceBox7 b).toKeyData 188160) := by
  intro i
  change |(((referenceBox7 b).toKeyData 188160).centre i : ℝ) -
    (((referenceBox7 b).toKeyData 188160).centre i : ℝ)| ≤ _
  rw [sub_self, abs_zero]
  exact_mod_cast referenceBox7_radius_nonneg b i

theorem referenceBox5_keyBase_nonempty (b : Bool) :
    (keyBase ((referenceBox5 b).toKeyData 19200)).Nonempty :=
  ⟨_, referenceBox5_centre_mem_keyBase b⟩

theorem referenceBox7_keyBase_nonempty (b : Bool) :
    (keyBase ((referenceBox7 b).toKeyData 188160)).Nonempty :=
  ⟨_, referenceBox7_centre_mem_keyBase b⟩

/-- Every tangential base interval has strictly positive length. -/
theorem referenceBox5_base_interval_pos (b : Bool) (i : Fin 4) :
    ((referenceBox5 b).toKeyData 19200).centre i.castSucc -
        ((referenceBox5 b).toKeyData 19200).radius i.castSucc <
      ((referenceBox5 b).toKeyData 19200).centre i.castSucc +
        ((referenceBox5 b).toKeyData 19200).radius i.castSucc := by
  linarith [referenceBox5_radius_pos b i]

theorem referenceBox7_base_interval_pos (b : Bool) (i : Fin 6) :
    ((referenceBox7 b).toKeyData 188160).centre i.castSucc -
        ((referenceBox7 b).toKeyData 188160).radius i.castSucc <
      ((referenceBox7 b).toKeyData 188160).centre i.castSucc +
        ((referenceBox7 b).toKeyData 188160).radius i.castSucc := by
  linarith [referenceBox7_radius_pos b i]

/-- The apex projects strictly inside each tangential base interval. -/
theorem referenceBox5_apex_projection_inside (b : Bool) (i : Fin 4) :
    ((referenceBox5 b).toKeyData 19200).centre i.castSucc -
        ((referenceBox5 b).toKeyData 19200).radius i.castSucc <
      ((referenceBox5 b).toKeyData 19200).apex i.castSucc ∧
    ((referenceBox5 b).toKeyData 19200).apex i.castSucc <
      ((referenceBox5 b).toKeyData 19200).centre i.castSucc +
        ((referenceBox5 b).toKeyData 19200).radius i.castSucc := by
  have ho := referenceBox5_offset b i
  have hw := referenceBox5_radius b i
  have hi := key5_offsets_inside i
  constructor <;> linarith [referenceBox5_radius_pos b i]

theorem referenceBox7_apex_projection_inside (b : Bool) (i : Fin 6) :
    ((referenceBox7 b).toKeyData 188160).centre i.castSucc -
        ((referenceBox7 b).toKeyData 188160).radius i.castSucc <
      ((referenceBox7 b).toKeyData 188160).apex i.castSucc ∧
    ((referenceBox7 b).toKeyData 188160).apex i.castSucc <
      ((referenceBox7 b).toKeyData 188160).centre i.castSucc +
        ((referenceBox7 b).toKeyData 188160).radius i.castSucc := by
  have ho := referenceBox7_offset b i
  have hw := referenceBox7_radius b i
  have hi := key7_offsets_inside i
  constructor <;> linarith [referenceBox7_radius_pos b i]

theorem referenceBox5_height_pos (b : Bool) :
    0 < ((referenceBox5 b).toKeyData 19200).apex 4 := by
  rw [referenceBox5_height]
  norm_num

theorem referenceBox7_height_pos (b : Bool) :
    0 < ((referenceBox7 b).toKeyData 188160).apex 6 := by
  rw [referenceBox7_height]
  norm_num

#print axioms canonical5_of_box_match
#print axioms canonical7_of_box_match
#print axioms referenceBox5_radius
#print axioms referenceBox7_radius
#print axioms referenceBox5_offset
#print axioms referenceBox7_offset
#print axioms referenceBox5_apex_projection_inside
#print axioms referenceBox7_apex_projection_inside

end SparseMonotiles.Canonical
