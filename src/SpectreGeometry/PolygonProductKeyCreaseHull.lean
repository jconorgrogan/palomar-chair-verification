module

public import SpectreGeometry.PolygonProductWholeKeyBinding
public import SpectreGeometry.PolygonProductKeyCreaseCompactness

@[expose] public section


namespace SpectreGeometry.ProductKeyReference
open SparseMonotiles SparseMonotiles.Contact ProductCrease PhysicalRegistration Set
open scoped InnerProductSpace
noncomputable section

def referenceVertex (j : Fin 2) :=
  euclideanPyramidVertex
    (keyPyramidLo ((referenceBox j).toKeyData referenceDenominator))
    (keyPyramidHi ((referenceBox j).toKeyData referenceDenominator))
    (rationalPoint ((referenceBox j).toKeyData referenceDenominator).apex)

theorem referenceSolid_convexHull_vertices (j : Fin 2) :
    referenceSolid j = convexHull ℝ (Set.range (referenceVertex j)) := by
  apply (pointPyramidEquiv 3).injective.image_injective
  rw [show referenceSolid j = keySolid ((referenceBox j).toKeyData referenceDenominator) from rfl,
    pointPyramidEquiv_image_keySolid _
      (by norm_num [referenceBox,BoxKey.toKeyData,rationalVertex,Fin.last])
      (by norm_num [referenceBox,BoxKey.toKeyData,rationalVertex,Fin.last]),
    pyramidSolid_eq_convexHull_vertices _ _ _ _ (fun i => (base_interval_pos j i).le)]
  rw [show (pointPyramidEquiv 3 : Point 4 → PyramidPoint 3) = (pointPyramidEquiv 3).toLinearMap from rfl,
    LinearMap.image_convexHull]
  congr 1
  rw [← range_pyramidVertex, ← Set.range_comp]
  apply congrArg Set.range
  funext v
  cases v with
  | none => rfl
  | some b =>
      apply Prod.ext
      · funext i
        simp [referenceVertex, euclideanPyramidVertex, euclideanPyramidCorner,
          pyramidVertex, pyramidCorner, Function.comp_def, pointPyramidEquiv_fst]
      · change 0 = euclideanPyramidCorner
          (keyPyramidLo ((referenceBox j).toKeyData referenceDenominator))
          (keyPyramidHi ((referenceBox j).toKeyData referenceDenominator)) b (Fin.last 3)
        exact (euclideanPyramidCorner_last _ _ b).symm

theorem branch_nonneg_iff_footprint (u : ProductKeySite) (x : EFour) :
    (∀ b, 0 ≤ productKeyBranchProfile u b x) ↔
    (∀ i : Fin 3,
      -productKeyEta/(productKeyPrime i false : ℝ) ≤ tangentCoord u x i ∧
      tangentCoord u x i ≤ productKeyEta/(productKeyPrime i true : ℝ)) := by
  have he : 0 < productKeyEta := by norm_num [productKeyEta]
  have hp (i : Fin 3) (b : Bool) : 0 < (productKeyPrime i b : ℝ) :=
    lt_of_lt_of_le (by norm_num) (product_key_prime_bounds i b).1
  constructor
  · intro h i
    have hl := h (i,false)
    have hh := h (i,true)
    simp only [productKeyBranchProfile, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_one_mul, neg_mul, neg_div] at hl hh
    change -productKeyEta / _ ≤ inner ℝ _ _ ∧ inner ℝ _ _ ≤ _
    constructor
    · apply (div_le_iff₀ (hp i false)).mpr
      have := (le_div_iff₀ he).mp (show -(1:ℝ) ≤ (productKeyPrime i false : ℝ) * inner ℝ (productKeyTangent u i) (x-productKeyCenter u) / productKeyEta from by linarith [hl])
      nlinarith
    · apply (le_div_iff₀ (hp i true)).mpr
      have := (div_le_iff₀ he).mp (show (productKeyPrime i true : ℝ) * inner ℝ (productKeyTangent u i) (x-productKeyCenter u) / productKeyEta ≤ (1:ℝ) from by linarith [hh])
      nlinarith
  · intro h b
    have hb := h b.1
    unfold productKeyBranchProfile
    change 0 ≤ 1 + (if b.2 then -1 else 1) * _ * tangentCoord u x b.1 / productKeyEta
    cases heq : b.2
    · simp only [Bool.false_eq_true, ite_false, one_mul]
      have ht := (div_le_iff₀ (hp b.1 false)).mp hb.1
      have hd : -(1:ℝ) ≤ (productKeyPrime b.1 false : ℝ) * tangentCoord u x b.1 / productKeyEta :=
        (le_div_iff₀ he).mpr (by nlinarith)
      linarith
    · simp only [ite_true, neg_one_mul, neg_mul, neg_div, one_mul]
      have ht := (le_div_iff₀ (hp b.1 true)).mp hb.2
      have hd : (productKeyPrime b.1 true : ℝ) * tangentCoord u x b.1 / productKeyEta ≤ 1 :=
        (div_le_iff₀ he).mpr (by nlinarith)
      linarith

theorem sideFace_subset_actualWholeKey (u : ProductKeySite) (b : ProductKeySide) :
    productKeySideFace u b ⊆ actualWholeKey u := by
  intro x hx
  have hfoot := (branch_nonneg_iff_footprint u x).mp (fun c => hx.2.1.trans (hx.2.2 c))
  have heq : inner ℝ (productKeySign u • productKeyOutwardNormal u) (x-productKeyCenter u) =
      productKeySign u * productKeyHeight u (x-productKeyCenter u) := by
    rw [real_inner_smul_left, hx.1]
  refine ⟨hfoot, ?_, heq.le⟩
  rw [heq]
  have ht := signed_pose_tent_height u ((productKeySignedAffineIsometry u).symm x)
  simp only [AffineIsometryEquiv.apply_symm_apply] at ht
  rw [ht]
  exact mul_nonneg (by unfold referenceHeight productKeyEta productKeyN; positivity) (le_max_left _ _)

theorem creaseComplex_subset_actualWholeKey (u : ProductKeySite) :
    creaseComplex u ⊆ actualWholeKey u := by
  intro x hx
  rcases hx with h | h
  · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp h
    exact sideFace_subset_actualWholeKey u b hb.1
  · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp h
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hb
    exact sideFace_subset_actualWholeKey u b hc.1

theorem referenceVertex_tangent (j : Fin 2) (v : Option (Fin 3 → Bool)) (i : Fin 3) :
    referenceVertex j v i.castSucc =
      match v with
      | none => 0
      | some b => if b i then productKeyEta/(productKeyPrime i true : ℝ)
          else -productKeyEta/(productKeyPrime i false : ℝ) := by
  cases v with
  | none => exact reference_apex_eq j i
  | some b => simp [referenceVertex, euclideanPyramidVertex,
      euclideanPyramidCorner_castSucc, reference_lo_eq, reference_hi_eq]

theorem referenceVertex_normal (j : Fin 2) (v : Option (Fin 3 → Bool)) :
    referenceVertex j v 3 = match v with | none => referenceHeight j | some _ => 0 := by
  cases v with
  | none => exact reference_height_eq j
  | some b => exact euclideanPyramidCorner_last _ _ b

theorem placed_referenceVertex_mem_crease (u : ProductKeySite) (v : Option (Fin 3 → Bool)) :
    productKeySignedAffineIsometry u (referenceVertex u.1 v) ∈ creaseComplex u := by
  let x := productKeySignedAffineIsometry u (referenceVertex u.1 v)
  have ht (i : Fin 3) : tangentCoord u x i = referenceVertex u.1 v i.castSucc :=
    product_key_signed_pose_tangent_coordinate u _ i
  have hn : normalCoord u x = productKeySign u * referenceVertex u.1 v 3 :=
    product_key_signed_pose_outward_coordinate u _
  have hp (i : Fin 3) (b : Bool) : 0 < (productKeyPrime i b : ℝ) := by
    linarith [(product_key_prime_bounds i b).1]
  have heta : 0 < productKeyEta := by norm_num [productKeyEta]
  cases v with
  | none =>
      have hb (b : ProductKeySide) : productKeyBranchProfile u b x = 1 := by
        change 1 + _ * _ * tangentCoord u x b.1 / _ = 1
        rw [ht, referenceVertex_tangent]
        simp
      have hf (b : ProductKeySide) : x ∈ productKeySideFace u b := by
        have hr : x ∈ productKeyBranchRegion u b := ⟨by rw [hb]; norm_num, fun c => by rw [hb,hb]⟩
        refine ⟨?_,hr⟩
        change normalCoord u x = _
        rw [hn, referenceVertex_normal]
        unfold productKeyHeight keyHeight
        rw [product_key_profile_eq_branch u b x hr, hb, productKeySignedLabel_real]
        unfold referenceHeight
        ring
      exact Or.inr (Set.mem_iUnion.mpr ⟨(0,false),Set.mem_iUnion.mpr
        ⟨⟨(1,false),by decide⟩,hf _,hf _⟩⟩)
  | some b =>
      have hfoot (i : Fin 3) :
          -productKeyEta/(productKeyPrime i false : ℝ) ≤ tangentCoord u x i ∧
          tangentCoord u x i ≤ productKeyEta/(productKeyPrime i true : ℝ) := by
        rw [ht,referenceVertex_tangent]
        have hlo := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr heta.le) (hp i false).le
        have hhi := div_nonneg heta.le (hp i true).le
        cases hb : b i <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] <;>
          exact ⟨by first | exact le_rfl | exact hlo.trans hhi,
            by first | exact le_rfl | exact hlo.trans hhi⟩
      have hnon := (branch_nonneg_iff_footprint u x).mpr hfoot
      let c : ProductKeySide := (0,b 0)
      have hc : productKeyBranchProfile u c x = 0 := by
        change 1 + (if b 0 then -1 else 1) * (productKeyPrime 0 (b 0) : ℝ) * tangentCoord u x 0 / productKeyEta = 0
        rw [ht,referenceVertex_tangent]
        cases hb : b 0 <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true]
        all_goals field_simp [ne_of_gt heta, ne_of_gt (hp 0 false), ne_of_gt (hp 0 true)] <;> ring
      have hr : x ∈ productKeyBranchRegion u c :=
        ⟨by rw [hc],fun d => by rw [hc]; exact hnon d⟩
      have hn0 : normalCoord u x = 0 := by rw [hn,referenceVertex_normal,mul_zero]
      have hg : x ∈ productKeyGraph u := by
        change normalCoord u x = _
        rw [hn0]
        unfold productKeyHeight keyHeight
        rw [product_key_profile_eq_branch u c x hr,hc,mul_zero]
      exact Or.inl (Set.mem_iUnion.mpr ⟨c,⟨hg,hr⟩,hn0⟩)

theorem actualWholeKey_convexHull_crease (u : ProductKeySite) :
    convexHull ℝ (creaseComplex u) = actualWholeKey u := by
  have hc : Convex ℝ (actualWholeKey u) := by
    rw [← signed_pose_image_reference, referenceSolid_convexHull_vertices]
    exact (convex_convexHull ℝ _).affine_image (productKeySignedAffineIsometry u).toAffineEquiv.toAffineMap
  apply Subset.antisymm (convexHull_min (creaseComplex_subset_actualWholeKey u) hc)
  rw [←signed_pose_image_reference,referenceSolid_convexHull_vertices]
  have he := (productKeySignedAffineIsometry u).toAffineEquiv.toAffineMap.image_convexHull
    (Set.range (referenceVertex u.1))
  change productKeySignedAffineIsometry u '' convexHull ℝ (Set.range (referenceVertex u.1)) = _ at he
  rw [he]
  apply convexHull_mono
  rintro x ⟨w,⟨v,rfl⟩,rfl⟩
  exact placed_referenceVertex_mem_crease u v


end
end SpectreGeometry.ProductKeyReference
