module

public import SpectreGeometry.PolygonProductKeyCreaseCompactness
public import SpectreGeometry.PolygonProductKeyCreaseSectors
public import Mathlib.Analysis.Convex.Topology

@[expose] public section


/-! Dense generic ridges of the actual 4D product keys. All strict witnesses
are computed from the recipe; density follows by convex interpolation. -/
namespace SpectreGeometry.ProductCrease
open SpectreGeometry PhysicalRegistration Set
open scoped InnerProductSpace
noncomputable section

def baseGeneric (u : ProductKeySite) (b : ProductKeySide) : Set EFour :=
  baseCrease u b ∩ {x | ∀ c, c ≠ b → 0 < productKeyBranchProfile u c x}
def sideGeneric (u : ProductKeySite) (b c : ProductKeySide) : Set EFour :=
  sideCrease u b c ∩ {x | 0 < productKeyBranchProfile u b x ∧
    ∀ d, d ≠ b → d ≠ c → productKeyBranchProfile u b x < productKeyBranchProfile u d x}

theorem profile_coordinate (u : ProductKeySite) (b : ProductKeySide)
    (v : Fin 3 → ℝ) (z : ℝ) :
    productKeyBranchProfile u b (keyCoordinatePoint u v z) =
    1 + (if b.2 then -1 else 1) * (productKeyPrime b.1 b.2 : ℝ) * v b.1 / productKeyEta := by
  unfold productKeyBranchProfile
  change 1 + _ * _ * tangentCoord u (keyCoordinatePoint u v z) b.1 / _ = _
  rw [keyCoordinatePoint_tangent]

def baseGenericWitness (u : ProductKeySite) (b : ProductKeySide) : EFour :=
  keyCoordinatePoint u (fun i => if i = b.1 then sideEndpoint b else 0) 0

theorem baseGenericWitness_zero (u : ProductKeySite) (b : ProductKeySide) :
    productKeyBranchProfile u b (baseGenericWitness u b) = 0 := by
  rcases b with ⟨i,e⟩
  fin_cases i <;> cases e <;>
    norm_num [baseGenericWitness,profile_coordinate,sideEndpoint,productKeyEta,
      productKeyPrime,productKeyPrimePairs]

theorem baseGenericWitness_other (u : ProductKeySite) (b c : ProductKeySide)
    (h : c ≠ b) : 0 < productKeyBranchProfile u c (baseGenericWitness u b) := by
  by_cases haxis : c.1 = b.1
  · rcases b with ⟨i,e⟩; rcases c with ⟨j,f⟩
    change j = i at haxis
    subst j
    fin_cases i <;> cases e <;> cases f <;>
      norm_num [baseGenericWitness,profile_coordinate,sideEndpoint,productKeyEta,
        productKeyPrime,productKeyPrimePairs] at *
  · norm_num [baseGenericWitness,profile_coordinate,haxis]

theorem baseGenericWitness_mem (u : ProductKeySite) (b : ProductKeySide) :
    baseGenericWitness u b ∈ baseGeneric u b := by
  have hall : ∀ c, 0 ≤ productKeyBranchProfile u c (baseGenericWitness u b) := by
    intro c
    by_cases h : c = b
    · subst c; rw [baseGenericWitness_zero]
    · exact (baseGenericWitness_other u b c h).le
  exact ⟨mem_baseCrease_of_branch_zero u b _ (by simp [baseGenericWitness])
    (baseGenericWitness_zero u b) hall,baseGenericWitness_other u b⟩

def sideGenericWitness (u : ProductKeySite) (b c : ProductKeySide) : EFour :=
  keyCoordinatePoint u
    (fun i => if i = b.1 then sideEndpoint b / 2 else if i = c.1 then sideEndpoint c / 2 else 0)
    (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN / 2)

theorem sideGenericWitness_left (u : ProductKeySite) (b c : ProductKeySide) :
    productKeyBranchProfile u b (sideGenericWitness u b c) = 1/2 := by
  rcases b with ⟨i,e⟩
  fin_cases i <;> cases e <;>
    norm_num [sideGenericWitness,profile_coordinate,sideEndpoint,productKeyEta,
      productKeyPrime,productKeyPrimePairs]

theorem sideGenericWitness_right (u : ProductKeySite) (b c : ProductKeySide)
    (h : b.1 ≠ c.1) : productKeyBranchProfile u c (sideGenericWitness u b c) = 1/2 := by
  simp only [sideGenericWitness,profile_coordinate,Ne.symm h,ite_false,ite_true]
  rcases c with ⟨j,f⟩
  fin_cases j <;> cases f <;>
    norm_num [sideEndpoint,productKeyEta,productKeyPrime,productKeyPrimePairs]

theorem sideGenericWitness_other (u : ProductKeySite) (b c d : ProductKeySide)
    (h : b.1 ≠ c.1) (hdb : d ≠ b) (hdc : d ≠ c) :
    1/2 < productKeyBranchProfile u d (sideGenericWitness u b c) := by
  by_cases haxisb : d.1 = b.1
  · have hp := baseGenericWitness_other u b d hdb
    have he : productKeyBranchProfile u d (sideGenericWitness u b c) =
        (1 + productKeyBranchProfile u d (baseGenericWitness u b)) / 2 := by
      simp only [sideGenericWitness,baseGenericWitness,profile_coordinate,haxisb,ite_true]
      ring
    rw [he]
    linarith
  · by_cases haxisc : d.1 = c.1
    · have hp := baseGenericWitness_other u c d hdc
      have he : productKeyBranchProfile u d (sideGenericWitness u b c) =
          (1 + productKeyBranchProfile u d (baseGenericWitness u c)) / 2 := by
        simp only [sideGenericWitness,baseGenericWitness,profile_coordinate,haxisb,ite_false,haxisc,Ne.symm h,ite_true]
        ring
      rw [he]
      linarith
    · norm_num [sideGenericWitness,profile_coordinate,haxisb,haxisc]

theorem sideGenericWitness_mem (u : ProductKeySite) (b c : ProductKeySide)
    (h : b.1 ≠ c.1) : sideGenericWitness u b c ∈ sideGeneric u b c := by
  let x := sideGenericWitness u b c
  have hb : productKeyBranchProfile u b x = 1/2 := sideGenericWitness_left u b c
  have hc : productKeyBranchProfile u c x = 1/2 := sideGenericWitness_right u b c h
  have hall : ∀ d, (1:ℝ)/2 ≤ productKeyBranchProfile u d x := by
    intro d
    by_cases hdb : d = b
    · subst d; exact hb.ge
    by_cases hdc : d = c
    · subst d; exact hc.ge
    exact (sideGenericWitness_other u b c d h hdb hdc).le
  have hbr : x ∈ productKeyBranchRegion u b := ⟨by rw [hb]; norm_num,fun d => by rw [hb]; exact hall d⟩
  have hcr : x ∈ productKeyBranchRegion u c := ⟨by rw [hc]; norm_num,fun d => by rw [hc]; exact hall d⟩
  have hg : x ∈ productKeyGraph u := by
    change normalCoord u x = _
    rw [product_key_height_eq_side_height u b x hbr,
      ProductCreaseSectors.sideHeight_eq_scaled_branch,hb]
    simp [x,sideGenericWitness]
    <;> ring
  exact ⟨⟨⟨hg,hbr⟩,⟨hg,hcr⟩⟩,by rw [hb]; norm_num,
    fun d hdb hdc => by rw [hb]; exact sideGenericWitness_other u b c d h hdb hdc⟩

theorem baseGeneric_nonempty (u : ProductKeySite) (b : ProductKeySide) :
    (baseGeneric u b).Nonempty := ⟨baseGenericWitness u b,baseGenericWitness_mem u b⟩
theorem sideGeneric_nonempty (u : ProductKeySite) (b c : ProductKeySide)
    (h : b.1 ≠ c.1) : (sideGeneric u b c).Nonempty :=
  ⟨sideGenericWitness u b c,sideGenericWitness_mem u b c h⟩

theorem openSegment_baseGeneric (u : ProductKeySite) (b : ProductKeySide)
    {w x : EFour} (hw : w ∈ baseGeneric u b) (hx : x ∈ baseCrease u b) :
    openSegment ℝ w x ⊆ baseGeneric u b := by
  rintro y ⟨r,q,hr,hq,hrq,rfl⟩
  refine ⟨baseCrease_convex u b hw.1 hx hr.le hq.le hrq,?_⟩
  intro c hcb
  rw [branchProfile_combination u c w x r q hrq]
  have hnonneg : 0 ≤ productKeyBranchProfile u c x := hx.1.2.1.trans (hx.1.2.2 c)
  exact add_pos_of_pos_of_nonneg (mul_pos hr (hw.2 c hcb)) (mul_nonneg hq.le hnonneg)

theorem openSegment_sideGeneric (u : ProductKeySite) (b c : ProductKeySide)
    {w x : EFour} (hw : w ∈ sideGeneric u b c) (hx : x ∈ sideCrease u b c) :
    openSegment ℝ w x ⊆ sideGeneric u b c := by
  rintro y ⟨r,q,hr,hq,hrq,rfl⟩
  refine ⟨sideCrease_convex u b c hw.1 hx hr.le hq.le hrq,?_,?_⟩
  · rw [branchProfile_combination u b w x r q hrq]
    exact add_pos_of_pos_of_nonneg (mul_pos hr hw.2.1) (mul_nonneg hq.le hx.1.2.1)
  · intro d hdb hdc
    rw [branchProfile_combination u b w x r q hrq,
      branchProfile_combination u d w x r q hrq]
    exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hw.2.2 d hdb hdc) hr)
      (mul_le_mul_of_nonneg_left (hx.1.2.2 d) hq.le)

theorem closure_baseGeneric (u : ProductKeySite) (b : ProductKeySide) :
    closure (baseGeneric u b) = baseCrease u b := by
  apply le_antisymm
  · exact closure_minimal (fun _ h => h.1) (baseCrease_isCompact u b).isClosed
  · intro x hx
    exact closure_mono (openSegment_baseGeneric u b (baseGenericWitness_mem u b) hx)
      (segment_subset_closure_openSegment (right_mem_segment ℝ (baseGenericWitness u b) x))

theorem closure_sideGeneric (u : ProductKeySite) (b c : ProductKeySide)
    (h : b.1 ≠ c.1) : closure (sideGeneric u b c) = sideCrease u b c := by
  apply le_antisymm
  · exact closure_minimal (fun _ h => h.1) (sideCrease_isCompact u b c).isClosed
  · intro x hx
    exact closure_mono (openSegment_sideGeneric u b c (sideGenericWitness_mem u b c h) hx)
      (segment_subset_closure_openSegment (right_mem_segment ℝ (sideGenericWitness u b c) x))

end
end SpectreGeometry.ProductCrease
