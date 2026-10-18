module

public import ProductClosure.NativeAngleSeparation
public import PhysicalRegistration.IsometryTransport

@[expose] public section

/-! Exact signed-permutation and integral-translation recovery from the
geometrically recovered complete native key frame. No lattice-frame premise
is used, and no orientation/properness conclusion is asserted here. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
noncomputable section
open PhysicalRegistration
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

/-- The genuine relative placement, mapping the second native copy into the
first native copy's coordinate system. -/
def relativePlacement (f g : Space m ≃ᵢ Space m) :
    Space m ≃ᵢ Space m := g.trans f.symm

/-- Ambient basis permutation; this is a column convention. -/
def nativeFrameIndex (u : Site S) : Option (Fin m) ≃ Fin (m + 1) :=
  (Equiv.optionCongr u.2.1).trans (finSuccEquiv' (normalIndex u.1)).symm

@[simp] theorem nativeFrameIndex_none (u : Site S) :
    nativeFrameIndex u none = normalIndex u.1 := by simp [nativeFrameIndex]

@[simp] theorem nativeFrameIndex_some (u : Site S) (j : Fin m) :
    nativeFrameIndex u (some j) = (normalIndex u.1).succAbove (u.2.1 j) := by
  simp [nativeFrameIndex]

/-- Column permutation forced by complete labelled key-frame matching. -/
def relativeFramePermutation (u v : Site S) : Equiv.Perm (Fin (m + 1)) :=
  (nativeFrameIndex v).symm.trans (nativeFrameIndex u)

@[simp] theorem relativeFramePermutation_native (u v : Site S)
    (j : Option (Fin m)) :
    relativeFramePermutation u v (nativeFrameIndex v j) = nativeFrameIndex u j := by
  simp [relativeFramePermutation]

@[simp] theorem relativeFramePermutation_normal (u v : Site S) :
    relativeFramePermutation u v (normalIndex v.1) = normalIndex u.1 := by
  simpa using relativeFramePermutation_native u v none

/-- An exact geometric frame predicate, stated on actual unit basis columns.
The permutation is not identified with a registered row permutation. -/
def HasIntegralSignedPermutation (e : Space m ≃ᵢ Space m) : Prop :=
  ∃ (p : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool)
    (t : Fin (m + 1) → ℤ),
    (∀ i, placedNormal e (EuclideanSpace.single i 1) =
      sign (b i) • EuclideanSpace.single (p i) 1) ∧
    e 0 = WithLp.toLp 2 (fun i => (t i : ℝ))

theorem placedNormal_eq_sub_zero (f : Space m ≃ᵢ Space m) (x : Space m) :
    placedNormal f x = f x - f 0 := by
  have h := f.toRealAffineIsometryEquiv.map_vsub x 0
  simpa [placedNormal] using h

theorem placedNormal_relative (f g : Space m ≃ᵢ Space m) (x : Space m) :
    placedNormal f (placedNormal (relativePlacement f g) x) = placedNormal g x := by
  rw [placedNormal_eq_sub_zero (relativePlacement f g), placedNormal_eq_sub_zero g]
  have h := f.toRealAffineIsometryEquiv.map_vsub
    (relativePlacement f g x) (relativePlacement f g 0)
  change placedNormal f (_ - _) = _ at h
  simpa [relativePlacement] using h

/-- Complete transported frame equations descend to the actual relative
isometry, before imposing any lattice condition. -/
theorem relativePlacement_key_frame (u v : Site S)
    (f g : Space m ≃ᵢ Space m)
    (ha : ∀ j, placedNormal g (siteAxis v j) = placedNormal f (siteAxis u j))
    (hn : placedNormal g (outward v.1) = -placedNormal f (outward u.1)) :
    (∀ j, placedNormal (relativePlacement f g) (siteAxis v j) = siteAxis u j) ∧
    placedNormal (relativePlacement f g) (outward v.1) = -outward u.1 := by
  constructor
  · intro j
    apply f.toRealAffineIsometryEquiv.linearIsometryEquiv.injective
    exact (placedNormal_relative f g _).trans (ha j)
  · apply f.toRealAffineIsometryEquiv.linearIsometryEquiv.injective
    simpa only [placedNormal, map_neg] using (placedNormal_relative f g (outward v.1)).trans hn

/-- The equal transported asymmetric offsets cancel exactly, leaving the
carrier facet centers matched by the same genuine relative isometry. -/
theorem relativePlacement_facetCenter (u v : Site S)
    (f g : Space m ≃ᵢ Space m)
    (ha : ∀ j, placedNormal g (siteAxis v j) = placedNormal f (siteAxis u j))
    (hc : f (siteCenter u) = g (siteCenter v)) :
    relativePlacement f g (facetCenter v.1) = facetCenter u.1 := by
  have hoff : placedNormal g (siteOffset v) = placedNormal f (siteOffset u) := by
    simp only [siteOffset, placedNormal, map_sum, map_smul]
    exact Finset.sum_congr rfl (fun j _ => congrArg (q0 j • ·) (ha j))
  have hcenter : f (facetCenter u.1) = g (facetCenter v.1) := by
    simp only [siteCenter] at hc
    change f.toRealAffineIsometryEquiv (facetCenter u.1 + siteOffset u) =
      g.toRealAffineIsometryEquiv (facetCenter v.1 + siteOffset v) at hc
    rw [affineIsometry_map_add f.toRealAffineIsometryEquiv,
      affineIsometry_map_add g.toRealAffineIsometryEquiv] at hc
    change f (facetCenter u.1) + placedNormal f (siteOffset u) =
      g (facetCenter v.1) + placedNormal g (siteOffset v) at hc
    rw [hoff] at hc
    exact add_right_cancel hc
  change f.symm (g (facetCenter v.1)) = facetCenter u.1
  rw [← hcenter, f.symm_apply_apply]

private theorem signed_basis_transport {m : ℕ}
    (L : Space m ≃ₗᵢ[ℝ] Space m) (i j : Fin (m + 1)) (a b : Bool)
    (h : L (sign a • EuclideanSpace.single i 1) = sign b • EuclideanSpace.single j 1) :
    ∃ c : Bool, L (EuclideanSpace.single i 1) = sign c • EuclideanSpace.single j 1 := by
  cases a <;> cases b
  · refine ⟨true, ?_⟩
    simpa [sign] using h
  · refine ⟨false, ?_⟩
    simpa [sign] using congrArg Neg.neg h
  · refine ⟨false, ?_⟩
    simpa [sign] using h
  · refine ⟨true, ?_⟩
    simpa [sign] using h

private theorem normalSign_eq_sign (F : Facet S) :
    ∃ b : Bool, normalSign F = sign b := ⟨F.positive, rfl⟩

/-- The full literal native frame forces the genuine relative linear map to
send every ambient unit basis column to the displayed signed permuted column. -/
theorem relativePlacement_signed_basis (u v : Site S)
    (f g : Space m ≃ᵢ Space m)
    (ha : ∀ j, placedNormal g (siteAxis v j) = placedNormal f (siteAxis u j))
    (hn : placedNormal g (outward v.1) = -placedNormal f (outward u.1)) :
    ∃ b : Fin (m + 1) → Bool, ∀ i,
      placedNormal (relativePlacement f g) (EuclideanSpace.single i 1) =
        sign (b i) • EuclideanSpace.single (relativeFramePermutation u v i) 1 := by
  have ⟨hta, htn⟩ := relativePlacement_key_frame u v f g ha hn
  have hb : ∀ i, ∃ b : Bool,
      placedNormal (relativePlacement f g) (EuclideanSpace.single i 1) =
        sign b • EuclideanSpace.single (relativeFramePermutation u v i) 1 := by
    intro i
    obtain ⟨j, rfl⟩ := (nativeFrameIndex v).surjective i
    rw [relativeFramePermutation_native]
    cases j with
    | none =>
      simp only [nativeFrameIndex_none]
      obtain ⟨bu, hbu⟩ := normalSign_eq_sign u.1
      obtain ⟨bv, hbv⟩ := normalSign_eq_sign v.1
      have hneg : -sign bu = sign (!bu) := by cases bu <;> norm_num [sign]
      simp only [outward, hbu, hbv, ← neg_smul, hneg] at htn
      exact signed_basis_transport _ _ _ bv (!bu) htn
    | some j =>
      simp only [nativeFrameIndex_some]
      exact signed_basis_transport _ _ _ (v.2.2 j) (u.2.2 j) (hta j)
  exact Classical.skolem.mp hb

private theorem facetCenter_normal_integer (F : Facet S) :
    ∃ z : ℤ, facetCenter F (normalIndex F) = (z : ℝ) :=
  ⟨Polycube.facetPlane F, Polycube.facetCenter_normal F⟩

private theorem facetCenter_tangent_half_integer (F : Facet S)
    (i : Fin (m + 1)) (hi : i ≠ normalIndex F) :
    ∃ z : ℤ, facetCenter F i = (z : ℝ) + 1 / 2 :=
  ⟨F.cell.val i, Polycube.facetCenter_tangent F i hi⟩

private theorem facetCenter_signed_difference_integer (u v : Site S)
    (i : Fin (m + 1)) (b : Bool) :
    ∃ z : ℤ, facetCenter u.1 (relativeFramePermutation u v i) -
      sign b * facetCenter v.1 i = (z : ℝ) := by
  by_cases hi : i = normalIndex v.1
  · subst i
    rw [relativeFramePermutation_normal]
    obtain ⟨zu, hu⟩ := facetCenter_normal_integer u.1
    obtain ⟨zv, hv⟩ := facetCenter_normal_integer v.1
    cases b
    · exact ⟨zu + zv, by simp [sign, hu, hv]⟩
    · exact ⟨zu - zv, by simp [sign, hu, hv]⟩
  · have hui : relativeFramePermutation u v i ≠ normalIndex u.1 := by
      intro h
      apply hi
      exact (relativeFramePermutation u v).injective
        (h.trans (relativeFramePermutation_normal u v).symm)
    obtain ⟨zu, hu⟩ := facetCenter_tangent_half_integer u.1 _ hui
    obtain ⟨zv, hv⟩ := facetCenter_tangent_half_integer v.1 i hi
    cases b
    · refine ⟨zu + zv + 1, ?_⟩
      simp only [sign, Bool.false_eq_true, ↓reduceIte, neg_one_mul, sub_neg_eq_add,
        hu, hv, Int.cast_add, Int.cast_one]
      ring
    · refine ⟨zu - zv, ?_⟩
      simp only [sign, ↓reduceIte, one_mul, hu, hv, Int.cast_sub]
      ring

/-- Integer translation is derived from facet-center matching. Tangent
half-integers cancel for both signs, and the normal coordinates are integers. -/
theorem relativePlacement_integer_translation (u v : Site S)
    (f g : Space m ≃ᵢ Space m)
    (ha : ∀ j, placedNormal g (siteAxis v j) = placedNormal f (siteAxis u j))
    (hn : placedNormal g (outward v.1) = -placedNormal f (outward u.1))
    (hc : f (siteCenter u) = g (siteCenter v)) :
    ∃ t : Fin (m + 1) → ℤ,
      relativePlacement f g 0 = WithLp.toLp 2 (fun i => (t i : ℝ)) := by
  obtain ⟨b, hb⟩ := relativePlacement_signed_basis u v f g ha hn
  have hcenter := relativePlacement_facetCenter u v f g ha hc
  have hcoord (i : Fin (m + 1)) :
      relativePlacement f g 0 (relativeFramePermutation u v i) =
        facetCenter u.1 (relativeFramePermutation u v i) - sign (b i) * facetCenter v.1 i := by
    have hinner := (relativePlacement f g).toRealAffineIsometryEquiv.linearIsometryEquiv.inner_map_map
      (EuclideanSpace.single i 1) (facetCenter v.1)
    change ⟪placedNormal (relativePlacement f g) (EuclideanSpace.single i 1),
      placedNormal (relativePlacement f g) (facetCenter v.1)⟫_ℝ = _ at hinner
    rw [hb i] at hinner
    simp only [real_inner_smul_left, EuclideanSpace.inner_single_left,
      map_one, one_mul] at hinner
    have hlin := congrArg (fun x : Space m => x (relativeFramePermutation u v i))
      (placedNormal_eq_sub_zero (relativePlacement f g) (facetCenter v.1))
    rw [hcenter] at hlin
    change placedNormal (relativePlacement f g) (facetCenter v.1)
      (relativeFramePermutation u v i) = facetCenter u.1 (relativeFramePermutation u v i) -
        relativePlacement f g 0 (relativeFramePermutation u v i) at hlin
    cases hi : b i <;> simp [sign, hi] at hinner ⊢ <;> linarith
  have hint : ∀ k : Fin (m + 1), ∃ z : ℤ, relativePlacement f g 0 k = (z : ℝ) := by
    intro k
    obtain ⟨i, rfl⟩ := (relativeFramePermutation u v).surjective k
    rw [hcoord]
    exact facetCenter_signed_difference_integer u v i (b i)
  choose t ht using hint
  refine ⟨t, ?_⟩
  ext i
  exact ht i

/-- Unrestricted placements with the geometrically determined exact key
frame have an actual integral signed-permutation relative isometry. -/
theorem relativePlacement_integral_signed_permutation (u v : Site S)
    (f g : Space m ≃ᵢ Space m)
    (ha : ∀ j, placedNormal g (siteAxis v j) = placedNormal f (siteAxis u j))
    (hn : placedNormal g (outward v.1) = -placedNormal f (outward u.1))
    (hc : f (siteCenter u) = g (siteCenter v)) :
    HasIntegralSignedPermutation (relativePlacement f g) := by
  obtain ⟨b, hb⟩ := relativePlacement_signed_basis u v f g ha hn
  obtain ⟨t, ht⟩ := relativePlacement_integer_translation u v f g ha hn hc
  exact ⟨relativeFramePermutation u v, b, t, hb, ht⟩


end
end ProductClosure.NativeCompiler
