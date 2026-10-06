module

public import SparseMonotiles.CarrierExistenceNested
public import SparseMonotiles.CarrierHierarchyRefinementLaw

@[expose] public section

/-! Legal nonemptiness reduces only to exact finite forward contact rules.
The world, nesting, dissection, and exhaustion are constructed, not premises. -/
namespace SparseMonotiles.CarrierHierarchy.Existence
open Contact

theorem move_eq_compose {d : ℕ} (t : ℤ) (p : Pose d) :
    move t p = compose (move t (rootPose d)) p := by
  rw [← move_compose, compose_root_left]

theorem normalize_move {d : ℕ} (t : ℤ) (p q : Pose d) :
    normalize (move t p) (move t q) = normalize p q := by
  rw [move_eq_compose t p, move_eq_compose t q, normalize_common_left]

theorem movedTiles_legal {d : ℕ} (t : ℤ) {S L : Set (Pose d)}
    (h : PatchLegal S L) : PatchLegal (movedTiles t S) L := by
  rintro p ⟨P, hP, rfl⟩ q ⟨Q, hQ, rfl⟩ hne hc
  rw [normalize_move]
  apply h P hP Q hQ
  · intro he
    subst Q
    exact hne rfl
  · rw [move_eq_compose t P, move_eq_compose t Q] at hc
    exact hc.remove_common_left (move t (rootPose d))

theorem stages_legal {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (C : Finset (Pose d)) (L : Set (Pose d))
    (hC : CoversCanonicalChildren σ C) (rules : ForwardRules C L)
    {S : Set (Pose d)} (hd : Disjoint S) (hl : PatchLegal S L) (n : ℕ) :
    PatchLegal (stages σ n S) L := by
  induction n with
  | zero => exact hl
  | succ n ih =>
      exact refinedTiles_legal σ C L _ (stages_disjoint σ n hd) hC rules ih

theorem patch_legal {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (C : Finset (Pose d)) (L : Set (Pose d))
    (hC : CoversCanonicalChildren σ C) (rules : ForwardRules C L) (n : ℕ) :
    PatchLegal (patch σ n) L := by
  apply stages_legal σ C L hC rules
  · exact patch_disjoint σ 0
  · intro p hp q hq hne _
    exact False.elim (hne (hp.trans hq.symm))

theorem ancestorPatch_legal {d : ℕ} (σ : Bits d → Equiv.Perm (Fin d))
    (C : Finset (Pose d)) (L : Set (Pose d))
    (hC : CoversCanonicalChildren σ C) (rules : ForwardRules C L) (m : ℕ) :
    PatchLegal (ancestorPatch σ m) L :=
  movedTiles_legal _ (patch_legal σ C L hC rules _)

/-- Every contacting pair lies in one finite legal ancestor patch. -/
theorem world_legal {d : ℕ} (hd : 0 < d) (σ : Bits d → Equiv.Perm (Fin d))
    (he : σ (fun _ => false) = Equiv.refl _)
    (C : Finset (Pose d)) (L : Set (Pose d))
    (hC : CoversCanonicalChildren σ C) (rules : ForwardRules C L) :
    (world hd σ he).Legal L := by
  rintro p ⟨m, hp⟩ q ⟨n, hq⟩ hne hc
  exact ancestorPatch_legal σ C L hC rules (max m n) p
    (ancestorPatch_mono hd σ he (le_max_left m n) hp) q
    (ancestorPatch_mono hd σ he (le_max_right m n) hq) hne hc

/-- Conditional only on finite substitution-contact closure, not an assumed
world or an assumed exhaustive hierarchy. -/
theorem legal_world_exists {d : ℕ} (hd : 0 < d)
    (σ : Bits d → Equiv.Perm (Fin d))
    (he : σ (fun _ => false) = Equiv.refl _)
    (C : Finset (Pose d)) (L : Set (Pose d))
    (hC : CoversCanonicalChildren σ C) (rules : ForwardRules C L) :
    ∃ W : RegisteredWorld d, W.Legal L :=
  ⟨world hd σ he, world_legal hd σ he C L hC rules⟩

#print axioms world_legal
#print axioms legal_world_exists
end SparseMonotiles.CarrierHierarchy.Existence
