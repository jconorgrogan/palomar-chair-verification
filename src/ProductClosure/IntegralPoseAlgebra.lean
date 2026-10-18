module

public import ProductClosure.SignedPermutationRegistration

@[expose] public section

/-! Integral signed-permutation poses form a group. Actual whole-key contacts
therefore register every tile in a key-companion component relative to its
chosen root. No connectedness or global-registration hypothesis is used. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

@[simp] theorem placedNormal_refl (x : Space m) :
    placedNormal (IsometryEquiv.refl (Space m)) x = x := by
  rw [placedNormal_eq_sub_zero]
  change x - 0 = x
  simp

theorem placedNormal_trans (e f : Space m ≃ᵢ Space m) (x : Space m) :
    placedNormal (e.trans f) x = placedNormal f (placedNormal e x) := by
  rw [placedNormal_eq_sub_zero e]
  have h := f.toRealAffineIsometryEquiv.map_vsub (e x) (e 0)
  change placedNormal f (e x - e 0) = _ at h
  simpa [placedNormal_eq_sub_zero] using h.symm

@[simp] theorem placedNormal_symm_apply (e : Space m ≃ᵢ Space m)
    (x : Space m) : placedNormal e.symm (placedNormal e x) = x := by
  rw [← placedNormal_trans]
  simp [placedNormal_eq_sub_zero]

@[simp] theorem placedNormal_apply_symm (e : Space m ≃ᵢ Space m)
    (x : Space m) : placedNormal e (placedNormal e.symm x) = x := by
  rw [← placedNormal_trans]
  simp [placedNormal_eq_sub_zero]

/-- A signed column equation gives the corresponding coordinate equation. -/
theorem signed_basis_coordinate (e : Space m ≃ᵢ Space m)
    (p : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool)
    (hb : ∀ i, placedNormal e (EuclideanSpace.single i 1) =
      sign (b i) • EuclideanSpace.single (p i) 1)
    (x : Space m) (i : Fin (m + 1)) :
    placedNormal e x (p i) = sign (b i) * x i := by
  have h := e.toRealAffineIsometryEquiv.linearIsometryEquiv.inner_map_map (EuclideanSpace.single i 1) x
  change ⟪placedNormal e (EuclideanSpace.single i 1), placedNormal e x⟫_ℝ = _ at h
  rw [hb i] at h
  simp only [real_inner_smul_left, EuclideanSpace.inner_single_left,
    map_one, one_mul] at h
  cases hi : b i <;> simp [sign, hi] at h ⊢ <;> linarith

/-- Coordinate evaluation for the exact witnesses in the defining predicate.
The permutation acts on columns; the translation is read at the output index. -/
theorem integral_signed_permutation_apply (e : Space m ≃ᵢ Space m)
    (p : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool)
    (t : Fin (m + 1) → ℤ)
    (hb : ∀ i, placedNormal e (EuclideanSpace.single i 1) =
      sign (b i) • EuclideanSpace.single (p i) 1)
    (ht : e 0 = WithLp.toLp 2 (fun i => (t i : ℝ)))
    (x : Space m) (i : Fin (m + 1)) :
    e x (p i) = sign (b i) * x i + (t (p i) : ℝ) := by
  have h := congrArg (fun y : Space m => y (p i)) (placedNormal_eq_sub_zero e x)
  rw [ht] at h
  change placedNormal e x (p i) = e x (p i) - (t (p i) : ℝ) at h
  rw [signed_basis_coordinate e p b hb] at h
  linarith

/-- Signed permutation linear parts preserve literal integer coordinates. -/
theorem signed_basis_integer_coordinates (e : Space m ≃ᵢ Space m)
    (p : Equiv.Perm (Fin (m + 1))) (b : Fin (m + 1) → Bool)
    (hb : ∀ i, placedNormal e (EuclideanSpace.single i 1) =
      sign (b i) • EuclideanSpace.single (p i) 1)
    (t : Fin (m + 1) → ℤ) :
    ∃ s : Fin (m + 1) → ℤ,
      placedNormal e (WithLp.toLp 2 (fun i => (t i : ℝ))) =
        WithLp.toLp 2 (fun i => (s i : ℝ)) := by
  have h : ∀ k, ∃ z : ℤ,
      placedNormal e (WithLp.toLp 2 (fun i => (t i : ℝ))) k = (z : ℝ) := by
    intro k
    obtain ⟨i, rfl⟩ := p.surjective k
    rw [signed_basis_coordinate e p b hb]
    cases hi : b i
    · exact ⟨-t i, by simp [sign]⟩
    · exact ⟨t i, by simp [sign]⟩
  choose s hs using h
  exact ⟨s, by ext k; exact hs k⟩

/-- The identity is an integral signed-permutation pose. -/
theorem HasIntegralSignedPermutation.refl :
    HasIntegralSignedPermutation (IsometryEquiv.refl (Space m)) := by
  refine ⟨Equiv.refl _, fun _ => true, fun _ => 0, ?_, ?_⟩
  · intro i
    simp [sign]
  · ext i
    change (0 : ℝ) = (0 : ℤ)
    norm_num

/-- Integral signed-permutation poses are closed under actual isometry
composition, with the same column convention as the defining predicate. -/
theorem HasIntegralSignedPermutation.trans {m : ℕ}
    {e f : Space m ≃ᵢ Space m} (he : HasIntegralSignedPermutation e)
    (hf : HasIntegralSignedPermutation f) :
    HasIntegralSignedPermutation (e.trans f) := by
  obtain ⟨p, b, t, hb, ht⟩ := he
  obtain ⟨q, c, s, hc, hs⟩ := hf
  obtain ⟨r, hr⟩ := signed_basis_integer_coordinates f q c hc t
  refine ⟨p.trans q, fun i => b i == c (p i), fun i => r i + s i, ?_, ?_⟩
  · intro i
    rw [placedNormal_trans, hb]
    change f.toRealAffineIsometryEquiv.linearIsometryEquiv
      (sign (b i) • EuclideanSpace.single (p i) 1) = _
    rw [map_smul]
    change sign (b i) • placedNormal f (EuclideanSpace.single (p i) 1) = _
    rw [hc]
    cases hbi : b i <;> cases hci : c (p i) <;> simp [sign, hbi, hci]
  · have hh := placedNormal_eq_sub_zero f (e 0)
    rw [ht, hr, hs] at hh
    ext i
    have hi := congrArg (fun x : Space m => x i) hh
    change f (e 0) i = ((r i + s i : ℤ) : ℝ)
    change (r i : ℝ) = f (WithLp.toLp 2 (fun j => (t j : ℝ))) i - (s i : ℝ) at hi
    rw [ht]
    push_cast
    linarith

/-- Integral signed-permutation poses are closed under inverse. -/
theorem HasIntegralSignedPermutation.symm {m : ℕ}
    {e : Space m ≃ᵢ Space m} (he : HasIntegralSignedPermutation e) :
    HasIntegralSignedPermutation e.symm := by
  obtain ⟨p, b, t, hb, ht⟩ := he
  have hbi : ∀ i, placedNormal e.symm (EuclideanSpace.single i 1) =
      sign (b (p.symm i)) • EuclideanSpace.single (p.symm i) 1 := by
    intro i
    apply e.toRealAffineIsometryEquiv.linearIsometryEquiv.injective
    change placedNormal e (placedNormal e.symm _) = placedNormal e (_ • _)
    rw [placedNormal_apply_symm]
    change _ = e.toRealAffineIsometryEquiv.linearIsometryEquiv (_ • _)
    rw [map_smul]
    change _ = sign (b (p.symm i)) • placedNormal e (EuclideanSpace.single (p.symm i) 1)
    rw [hb]
    cases hi : b (p.symm i) <;> simp [sign]
  obtain ⟨s, hs⟩ := signed_basis_integer_coordinates e.symm p.symm
    (fun i => b (p.symm i)) hbi t
  refine ⟨p.symm, fun i => b (p.symm i), fun i => -s i, hbi, ?_⟩
  have h := placedNormal_eq_sub_zero e.symm (e 0)
  rw [e.symm_apply_apply, ht, hs] at h
  ext i
  have hi := congrArg (fun x : Space m => x i) h
  change e.symm 0 i = ((-s i : ℤ) : ℝ)
  change (s i : ℝ) = (0 : Space m) i - e.symm 0 i at hi
  simp only [PiLp.zero_apply, zero_sub] at hi
  push_cast
  linarith


@[simp] theorem relativePlacement_self (f : Space m ≃ᵢ Space m) :
    relativePlacement f f = IsometryEquiv.refl (Space m) := by
  apply IsometryEquiv.ext
  intro x
  exact f.symm_apply_apply x

@[simp] theorem relativePlacement_symm (f g : Space m ≃ᵢ Space m) :
    (relativePlacement f g).symm = relativePlacement g f := by
  apply IsometryEquiv.ext
  intro x
  rfl

/-- Relative poses compose in the displayed order, because `trans` applies
its left argument first. -/
theorem relativePlacement_trans (f g h : Space m ≃ᵢ Space m) :
    (relativePlacement g h).trans (relativePlacement f g) = relativePlacement f h := by
  apply IsometryEquiv.ext
  intro x
  change f.symm (g (g.symm (h x))) = f.symm (h x)
  rw [g.apply_symm_apply]

theorem relative_integral_refl (f : Space m ≃ᵢ Space m) :
    HasIntegralSignedPermutation (relativePlacement f f) := by
  rw [relativePlacement_self]
  exact HasIntegralSignedPermutation.refl

theorem relative_integral_symm {f g : Space m ≃ᵢ Space m}
    (h : HasIntegralSignedPermutation (relativePlacement f g)) :
    HasIntegralSignedPermutation (relativePlacement g f) := by
  simpa only [relativePlacement_symm] using h.symm

theorem relative_integral_trans {f g h : Space m ≃ᵢ Space m}
    (hfg : HasIntegralSignedPermutation (relativePlacement f g))
    (hgh : HasIntegralSignedPermutation (relativePlacement g h)) :
    HasIntegralSignedPermutation (relativePlacement f h) := by
  simpa only [relativePlacement_trans] using hgh.trans hfg


end
end ProductClosure.NativeCompiler
